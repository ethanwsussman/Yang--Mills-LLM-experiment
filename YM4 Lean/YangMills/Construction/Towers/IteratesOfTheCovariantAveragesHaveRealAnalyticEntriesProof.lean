import YangMills.Construction.Towers.ChainOfTheComplexIterateDifferentials
import YangMills.Construction.Towers.IteratesOfTheCovariantAveragesHaveRealAnalyticEntries
import YangMills.Construction.Towers.PlaquettesAndSumsOfATower
import YangMills.Construction.Towers.SecondOrderOfACompositeAtOneProof
import YangMills.Construction.Towers.StepOfTheCovariantAveragesHasRealAnalyticEntries
import YangMills.Construction.Towers.SumsProductsAndCompositesOfRealAnalyticFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set Filter Coordinates Matrices Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces Tower
open scoped Topology Matrix.Norms.L2Operator
namespace CovariantIterates
structure Inputs : Prop where
  step : SmoothingStepAnalyticEntries
  iterate : SmoothingIterAnalyticNearOne
  algebra : AnalyticFieldFunctionsClosed
  bonds : BondSetFields.ProductStructureHolds
  spaces : FiniteSideFormSpaces
  sums : FaceSums.FacesAndPairings
  linear : RealLinearMaps.RealLinearMapsStatement
  levels : LevelwiseMeans.LevelwiseMeansHold
  formed : IteratedMeans.IteratedMeansHold
  chain : ComplexIterDerivChain
  holomorphy : HolomorphyClosureStatement
def herPart (X : ComplexMatrix2) : ComplexMatrix2 := (1 / 2 : ℂ) • (X + X.conjTranspose)
def antiherPart (X : ComplexMatrix2) : ComplexMatrix2 := (-Complex.I / 2) • (X - X.conjTranspose)
theorem herPart_add (X Y : ComplexMatrix2) : herPart (X + Y) = herPart X + herPart Y := by
  simp only [herPart, Matrix.conjTranspose_add]
  module
theorem antiherPart_add (X Y : ComplexMatrix2) :
    antiherPart (X + Y) = antiherPart X + antiherPart Y := by
  simp only [antiherPart, Matrix.conjTranspose_add]
  module
theorem herPart_smul (c : ℂ) (X : ComplexMatrix2) :
    herPart (c • X) = c.re • herPart X - c.im • antiherPart X := by
  ext i j
  simp only [herPart, antiherPart, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.conjTranspose_apply, Matrix.conjTranspose_smul]
  apply Complex.ext <;> simp <;> ring
theorem antiherPart_smul (c : ℂ) (X : ComplexMatrix2) :
    antiherPart (c • X) = c.im • herPart X + c.re • antiherPart X := by
  ext i j
  simp only [herPart, antiherPart, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.conjTranspose_apply, Matrix.conjTranspose_smul]
  apply Complex.ext <;> simp <;> ring
def complexify (φ : ComplexMatrix2 →ₗ[ℝ] ℝ) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun X := (φ (herPart X) : ℂ) + Complex.I * (φ (antiherPart X) : ℂ)
  map_add' X Y := by
    simp only [herPart_add, antiherPart_add, map_add]
    push_cast
    ring
  map_smul' c X := by
    simp only [herPart_smul, antiherPart_smul, map_add, map_sub, map_smul, smul_eq_mul,
      RingHom.id_apply]
    apply Complex.ext <;> simp
    ring
theorem complexify_of_isHermitian (φ : ComplexMatrix2 →ₗ[ℝ] ℝ) {X : ComplexMatrix2}
    (hX : X.IsHermitian) : complexify φ X = (φ X : ℂ) := by
  have h₁ : herPart X = X := by
    simp only [herPart, hX.eq]
    module
  have h₂ : antiherPart X = 0 := by
    simp only [antiherPart, hX.eq, sub_self, smul_zero]
  change (φ (herPart X) : ℂ) + Complex.I * (φ (antiherPart X) : ℂ) = _
  rw [h₁, h₂]
  simp
theorem inv_eq_conjTranspose_of_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.specialUnitary) :
    X⁻¹ = X.conjTranspose := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_eq_conjTranspose_of_mem_specialUnitary <;> assumption
theorem isHermitian_conjugateBy {g A : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary)
    (hA : A.IsHermitian) : (ComplexMatrix2.conjugateBy g A).IsHermitian := by
  have e : (g.conjTranspose).conjTranspose = g := Matrix.conjTranspose_conjTranspose g
  simp only [Matrix.IsHermitian, ComplexMatrix2.conjugateBy, inv_eq_conjTranspose_of_mem hg,
    Matrix.conjTranspose_mul, e, hA.eq, mul_assoc]
theorem isHermitian_of_mem_hermitianTraceless {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.hermitianTraceless) : X.IsHermitian := h.1.symm
section Difference
variable {L n k j : ℕ}
theorem holomorphic_firstCoord {ι κ : Type} [Fintype ι] [Fintype κ]
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {N : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (h : IsHolomorphicToCoords b ComplexCoordinates.matrixEquiv W N) :
    IsHolomorphicToCoords b (Equiv.refl (ComplexCoordinates 1)) W
      fun q _ => ComplexCoordinates.matrixEquiv (N q) 0 := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.isHolomorphicToCoords_firstEntry <;> assumption
abbrev fieldOfPoint (q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2) : Edge L n k j → ComplexMatrix2 :=
  fieldOfPositiveValues (groupComponent q)
theorem analytic_of_holomorphic_hermitian (hH : HolomorphyClosureStatement)
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)} {F : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (h0 : IsAnalyticFieldFunction 𝒰 fun _ => (0 : ℝ))
    (hF : ∀ (_ : Fintype (PositiveEdge L n k j)) (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless),
      IsHolomorphicToMatrixEntries b (GroupLieProduct (PositiveEdge L n k j) Empty)
        fun q => F (fieldOfPoint q))
    (hh : ∀ U ∈ 𝒰, (F U).IsHermitian) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ) :
    IsAnalyticFieldFunction 𝒰 fun U => φ (F U) := by
  obtain ⟨hO, inst, hE, hX⟩ := h0
  refine ⟨hO, inst, hE, fun p hp => ?_⟩
  obtain ⟨𝒳, hp𝒳, h𝒳, hsub, -⟩ := hX p hp
  refine ⟨𝒳, hp𝒳, h𝒳, hsub, fun q _ => ComplexCoordinates.matrixEquiv
    ((complexify φ).smulRight (1 : ComplexMatrix2) (F (fieldOfPoint q))) 0,
    fun b => ?_, fun q hq => ?_⟩
  · have hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (PositiveEdge L n k j) Empty)
        (GroupLieProduct (PositiveEdge L n k j) Empty) := ⟨univ, isOpen_univ, by simp⟩
    obtain ⟨-, -, -, -, hl, -, -, -, -, hm, -⟩ := hH _ _ b _ hW
    have hs : 𝒳 ⊆ GroupLieProduct (PositiveEdge L n k j) Empty := by
      obtain ⟨O, -, e⟩ := h𝒳
      rw [e]
      exact inter_subset_right
    exact holomorphic_firstCoord (hm _ hs h𝒳 _ (hl _ _ (hF inst b)))
  · have hU : fieldOfPoint q ∈ 𝒰 := hsub hq
    funext i
    have e0 : ComplexCoordinates.entryIndex.symm (0 : Fin 4) = ((0 : Fin 2), (0 : Fin 2)) := rfl
    show ((complexify φ).smulRight (1 : ComplexMatrix2) (F (fieldOfPoint q)))
      (ComplexCoordinates.entryIndex.symm 0).1 (ComplexCoordinates.entryIndex.symm 0).2 = _
    rw [e0]
    simp [complexify_of_isHermitian φ (hh _ hU)]
theorem fieldOfPoint_apply (q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2)
    {c : Edge L n k j} (h : c.IsPositivelyOriented) :
    fieldOfPoint q c = q (.inl ⟨c, h⟩) := by
  simp [fieldOfPositiveValues, h, groupComponent]
theorem holomorphic_conjugateBy [Fintype (PositiveEdge L n k j)]
    (hH : HolomorphyClosureStatement) (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {c : Edge L n k j} (h : c.IsPositivelyOriented) (A : ComplexMatrix2) :
    IsHolomorphicToMatrixEntries b (GroupLieProduct (PositiveEdge L n k j) Empty)
      fun q => ComplexMatrix2.conjugateBy (fieldOfPoint q c) A := by
  have hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (PositiveEdge L n k j) Empty)
      (GroupLieProduct (PositiveEdge L n k j) Empty) := ⟨univ, isOpen_univ, by simp⟩
  obtain ⟨hc, hm, -, hp, -, hi, -⟩ := hH _ _ b _ hW
  have e : (fun q : PositiveEdge L n k j ⊕ Empty → ComplexMatrix2 =>
      ComplexMatrix2.conjugateBy (fieldOfPoint q c) A) =
      fun q => q (.inl ⟨c, h⟩) * A * (q (.inl ⟨c, h⟩))⁻¹ := by
    funext q
    rw [fieldOfPoint_apply q h]
    rfl
  rw [e]
  refine hp _ _ (hp _ _ (hm _) (hc A)) (hi _ (hm _) fun q hq => ?_)
  have hd : (q (.inl ⟨c, h⟩)).det = 1 := hq (.inl ⟨c, h⟩)
  rw [hd]
  exact isUnit_one
theorem covDiff_entries_analytic (hH : HolomorphyClosureStatement)
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)} (h0 : IsAnalyticFieldFunction 𝒰 fun _ => (0 : ℝ))
    (l : vertexFunctionSpace L n k j) (c : PositiveEdge L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ) :
    IsAnalyticFieldFunction 𝒰 fun W =>
      φ (covDiff W (l : Vertex L n k j → ComplexMatrix2) c.1) := by
  have e : (fun W => φ (covDiff W (l : Vertex L n k j → ComplexMatrix2) c.1)) =
      fun W : Edge L n k j → ComplexMatrix2 =>
        φ (ComplexMatrix2.conjugateBy (W c.1) ((l : Vertex L n k j → ComplexMatrix2) c.1.target) -
        (l : Vertex L n k j → ComplexMatrix2) c.1.source) := by
    funext W
    simp [covDiff, extendOddly, c.2]
  rw [e]
  refine analytic_of_holomorphic_hermitian hH h0
    (F := fun W => ComplexMatrix2.conjugateBy (W c.1) ((l : Vertex L n k j → ComplexMatrix2) c.1.target) -
      (l : Vertex L n k j → ComplexMatrix2) c.1.source) (fun _ b => ?_) (fun U hU => ?_) φ
  · have hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (PositiveEdge L n k j) Empty)
        (GroupLieProduct (PositiveEdge L n k j) Empty) := ⟨univ, isOpen_univ, by simp⟩
    obtain ⟨hconst, -, ha, -⟩ := hH _ _ b _ hW
    simpa only [sub_eq_add_neg] using ha _ _ (holomorphic_conjugateBy hH b c.2 _) (hconst _)
  · have hU' : U ∈ fieldSpace L n k j := h0.1.1 hU
    exact (isHermitian_conjugateBy (hU'.1 c.1 (mem_univ _))
      (isHermitian_of_mem_hermitianTraceless (l.2 _ (mem_univ _)))).sub
        (isHermitian_of_mem_hermitianTraceless (l.2 _ (mem_univ _)))
end Difference
theorem exists_linear_coords {W α : Type} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [Fintype α] [DecidableEq α] (ι : W →ₗ[ℝ] α → ComplexMatrix2) (hι : Function.Injective ι) :
    ∃ (d : ℕ) (e : Fin d → W) (ψ : Fin d → α → ComplexMatrix2 →ₗ[ℝ] ℝ),
      ∀ x, x = ∑ a, (∑ i, ψ a i (ι x i)) • e a := by
  obtain ⟨r, hr⟩ := ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hι)
  let b := Module.finBasis ℝ W
  refine ⟨_, b, fun a i => (b.coord a) ∘ₗ r ∘ₗ LinearMap.single ℝ (fun _ : α => ComplexMatrix2) i,
    fun x => ?_⟩
  have h1 : ∑ i, LinearMap.single ℝ (fun _ : α => ComplexMatrix2) i (ι x i) = ι x := by
    simpa using Finset.univ_sum_single (ι x)
  have h2 : r (ι x) = x := LinearMap.congr_fun hr x
  have hc : ∀ a, ∑ i, ((b.coord a) ∘ₗ r ∘ₗ LinearMap.single ℝ (fun _ : α => ComplexMatrix2) i) (ι x i) =
      b.repr x a := by
    intro a
    calc ∑ i, ((b.coord a) ∘ₗ r ∘ₗ LinearMap.single ℝ (fun _ : α => ComplexMatrix2) i) (ι x i)
        = b.coord a (r (∑ i, LinearMap.single ℝ (fun _ : α => ComplexMatrix2) i (ι x i))) := by
          simp only [map_sum, LinearMap.comp_apply]
      _ = b.repr x a := by
          rw [h1, h2]
          rfl
  simp only [hc]
  exact (b.sum_repr x).symm
section Functions
variable {L n k : ℕ}
structure AnalyticAlgebra (𝒰 : Set (Edge L n k 0 → ComplexMatrix2)) : Prop where
  const (c : ℝ) : IsAnalyticFieldFunction 𝒰 fun _ => c
  add {F H : (Edge L n k 0 → ComplexMatrix2) → ℝ} : IsAnalyticFieldFunction 𝒰 F →
    IsAnalyticFieldFunction 𝒰 H → IsAnalyticFieldFunction 𝒰 fun U => F U + H U
  mul {F H : (Edge L n k 0 → ComplexMatrix2) → ℝ} : IsAnalyticFieldFunction 𝒰 F →
    IsAnalyticFieldFunction 𝒰 H → IsAnalyticFieldFunction 𝒰 fun U => F U * H U
  congr {F H : (Edge L n k 0 → ComplexMatrix2) → ℝ} : IsAnalyticFieldFunction 𝒰 F → EqOn F H 𝒰 →
    IsAnalyticFieldFunction 𝒰 H
theorem AnalyticAlgebra.sum {𝒰 : Set (Edge L n k 0 → ComplexMatrix2)} (h : AnalyticAlgebra 𝒰)
    {ι : Type*} (s : Finset ι) {H : ι → (Edge L n k 0 → ComplexMatrix2) → ℝ}
    (hH : ∀ a ∈ s, IsAnalyticFieldFunction 𝒰 (H a)) :
    IsAnalyticFieldFunction 𝒰 fun U => ∑ a ∈ s, H a U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact h.add (hH a (Finset.mem_insert_self a s))
      (ih fun b hb => hH b (Finset.mem_insert_of_mem hb))
theorem analytic_of_linear_expansion {𝒰 : Set (Edge L n k 0 → ComplexMatrix2)} (alg : AnalyticAlgebra 𝒰)
    {W α : Type} [AddCommGroup W] [Module ℝ W] [Fintype α] {d : ℕ} (e : Fin d → W)
    (ψ : Fin d → α → ComplexMatrix2 →ₗ[ℝ] ℝ) (ι : W → α → ComplexMatrix2)
    (hexp : ∀ x, x = ∑ a, (∑ i, ψ a i (ι x i)) • e a)
    {H : (Edge L n k 0 → ComplexMatrix2) → W → ComplexMatrix2}
    (hlin : ∀ U ∈ 𝒰, ∃ T : W →ₗ[ℝ] ComplexMatrix2, ∀ w, T w = H U w)
    (hH : ∀ (w : W) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ), IsAnalyticFieldFunction 𝒰 fun U => φ (H U w))
    {Y : (Edge L n k 0 → ComplexMatrix2) → α → ComplexMatrix2}
    (hY : ∀ (i : α) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ), IsAnalyticFieldFunction 𝒰 fun U => φ (Y U i))
    {R : (Edge L n k 0 → ComplexMatrix2) → ComplexMatrix2} (hR : ∀ U ∈ 𝒰, ∃ x : W, ι x = Y U ∧ R U = H U x)
    (φ : ComplexMatrix2 →ₗ[ℝ] ℝ) : IsAnalyticFieldFunction 𝒰 fun U => φ (R U) := by
  refine alg.congr (alg.sum Finset.univ (H := fun a U => (∑ i, ψ a i (Y U i)) * φ (H U (e a)))
    fun a _ => alg.mul (alg.sum Finset.univ fun i _ => hY i (ψ a i)) (hH (e a) φ)) fun U hU => ?_
  obtain ⟨x, hx, hr⟩ := hR U hU
  obtain ⟨T, hT⟩ := hlin U hU
  have h : H U x = ∑ a, (∑ i, ψ a i (Y U i)) • H U (e a) := by
    rw [← hT x, ← hx, congrArg T (hexp x), map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, hT]
  show ∑ a, (∑ i, ψ a i (Y U i)) * φ (H U (e a)) = φ (R U)
  rw [hr, h, map_sum]
  simp only [map_smul, smul_eq_mul]
theorem analytic_at_edgeForm (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {j : ℕ} (hj : j ≤ k) {𝒰 : Set (Edge L n k 0 → ComplexMatrix2)} (alg : AnalyticAlgebra 𝒰)
    {H : (Edge L n k 0 → ComplexMatrix2) → (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (hlin : ∀ U ∈ 𝒰, ∃ T : edgeFormSpace L n k j →ₗ[ℝ] ComplexMatrix2, ∀ w : edgeFormSpace L n k j,
      T w = H U (w : Edge L n k j → ComplexMatrix2))
    (hH : ∀ (w : edgeFormSpace L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
      IsAnalyticFieldFunction 𝒰 fun U => φ (H U (w : Edge L n k j → ComplexMatrix2)))
    {Y : (Edge L n k 0 → ComplexMatrix2) → Edge L n k j → ComplexMatrix2}
    (hY : ∀ (c : PositiveEdge L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
      IsAnalyticFieldFunction 𝒰 fun U => φ (Y U c.1))
    (hm : ∀ U ∈ 𝒰, Y U ∈ edgeFormSpace L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ) :
    IsAnalyticFieldFunction 𝒰 fun U => φ (H U (Y U)) := by
  classical
  obtain ⟨hfin, fd, -, -⟩ := G.spaces L n k j hL hn hj
  let _ : Fintype (PositiveEdge L n k j) := Fintype.ofFinite _
  let ι : edgeFormSpace L n k j →ₗ[ℝ] PositiveEdge L n k j → ComplexMatrix2 :=
    { toFun := fun x => restrictToPositiveEdges (x : Edge L n k j → ComplexMatrix2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hι : Function.Injective ι := by
    intro x y h
    refine Subtype.ext (funext fun b => ?_)
    obtain ⟨μ, h' | h'⟩ := b.isNeighbour
    · exact congrFun h ⟨b, μ, h'⟩
    · have hb : b.opposite.IsPositivelyOriented := by
        refine ⟨μ, ?_⟩
        change b.source - b.target = _
        rw [← neg_sub, h', neg_neg]
      have e := congrFun h ⟨b.opposite, hb⟩
      have e' : (x : Edge L n k j → ComplexMatrix2) b.opposite = (y : Edge L n k j → ComplexMatrix2) b.opposite := e
      rw [x.2.2 b, y.2.2 b] at e'
      exact neg_injective e'
  obtain ⟨d, e, ψ, hexp⟩ := exists_linear_coords ι hι
  exact analytic_of_linear_expansion alg e ψ ι hexp (H := fun U w => H U (w : Edge L n k j → ComplexMatrix2))
    (Y := fun U => restrictToPositiveEdges (Y U)) (R := fun U => H U (Y U)) hlin hH hY
    (fun U hU => ⟨⟨Y U, hm U hU⟩, rfl, rfl⟩) φ
theorem analytic_at_vertexFunction (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j ≤ k) {𝒰 : Set (Edge L n k 0 → ComplexMatrix2)} (alg : AnalyticAlgebra 𝒰)
    {H : (Edge L n k 0 → ComplexMatrix2) → (Vertex L n k j → ComplexMatrix2) → ComplexMatrix2}
    (hlin : ∀ U ∈ 𝒰, ∃ T : vertexFunctionSpace L n k j →ₗ[ℝ] ComplexMatrix2,
      ∀ w : vertexFunctionSpace L n k j, T w = H U (w : Vertex L n k j → ComplexMatrix2))
    (hH : ∀ (w : vertexFunctionSpace L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
      IsAnalyticFieldFunction 𝒰 fun U => φ (H U (w : Vertex L n k j → ComplexMatrix2)))
    {Y : (Edge L n k 0 → ComplexMatrix2) → Vertex L n k j → ComplexMatrix2}
    (hY : ∀ (y : Vertex L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
      IsAnalyticFieldFunction 𝒰 fun U => φ (Y U y))
    (hm : ∀ U ∈ 𝒰, Y U ∈ vertexFunctionSpace L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ) :
    IsAnalyticFieldFunction 𝒰 fun U => φ (H U (Y U)) := by
  classical
  have hfin : Finite (Vertex L n k j) := Set.finite_univ_iff.mp
    (((G.sums L hL k j hj).1 n hn).2.1 Set.univ).2.1
  let _ : Fintype (Vertex L n k j) := Fintype.ofFinite _
  have : FiniteDimensional ℝ (Vertex L n k j → ComplexMatrix2) := inferInstance
  obtain ⟨d, e, ψ, hexp⟩ := exists_linear_coords (vertexFunctionSpace L n k j).subtype
    Subtype.val_injective
  exact analytic_of_linear_expansion alg e ψ (vertexFunctionSpace L n k j).subtype hexp
    (H := fun U w => H U (w : Vertex L n k j → ComplexMatrix2)) (Y := Y) (R := fun U => H U (Y U)) hlin hH hY
    (fun U hU => ⟨⟨Y U, hm U hU⟩, rfl, rfl⟩) φ
end Functions
section Sets
variable {L n k j : ℕ}
theorem isOpenFieldSet_iff (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : j ≤ k) (𝒰 : Set (Edge L n k j → ComplexMatrix2)) :
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ↔
      𝒰 ⊆ fieldSpace L n k j ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k j) 𝒰 := by
  have A := ((G.bonds L hL k j hj).1 n hn).2.2.2.2.2.2.2.2.1
  exact ⟨fun h => ⟨h.1, (A 𝒰 h.1).2 h.2⟩, fun h => ⟨h.1, (A 𝒰 h.1).1 h.2⟩⟩
theorem trivialField_mem_fieldSpace : trivialField L n k j ∈ fieldSpace L n k j := by apply _root_.YangMills.Construction.Tower.CompositeSecondOrder.trivialField_mem <;> assumption
theorem fieldSpace_isOpenNhdOfOne (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) : IsOpenNhdOfOne (fieldSpace L n k j) :=
  ⟨(isOpenFieldSet_iff G hL hn hj _).2 ⟨subset_rfl, univ, isOpen_univ, by simp⟩,
    trivialField_mem_fieldSpace⟩
theorem eventuallyNearIdentity_mem (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) {𝒰 : Set (Edge L n k j → ComplexMatrix2)} (h : IsOpenNhdOfOne 𝒰) :
    EventuallyNearIdentity (fieldSpace L n k j) fun V => V ∈ 𝒰 := by
  obtain ⟨-, O, hO, e⟩ := (isOpenFieldSet_iff G hL hn hj 𝒰).1 h.1
  have h2 : trivialField L n k j ∈ O ∩ fieldSpace L n k j := by
    rw [← e]
    exact h.2
  show {V | V ∈ 𝒰} ∈ 𝓝[fieldSpace L n k j] (trivialField L n k j)
  exact mem_nhdsWithin.2 ⟨O, hO, h2.1, fun V hV => by
    show V ∈ 𝒰
    rw [e]
    exact hV⟩
theorem exists_open_of_eventually (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hj : j ≤ k) {𝒰₀ : Set (Edge L n k j → ComplexMatrix2)}
    {P : (Edge L n k j → ComplexMatrix2) → Prop}
    (h : IsOpenNhdOfOne 𝒰₀) (hne : EventuallyNearIdentity (fieldSpace L n k j) P) :
    ∃ 𝒰 : Set (Edge L n k j → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧ 𝒰 ⊆ 𝒰₀ ∧ ∀ W ∈ 𝒰, P W := by
  have hop := isOpenFieldSet_iff (n := n) (k := k) (j := j) G hL hn hj
  obtain ⟨-, O₀, hO₀, e₀⟩ := (hop 𝒰₀).1 h.1
  have hne' : {W | P W} ∈ 𝓝[fieldSpace L n k j] (trivialField L n k j) := hne
  obtain ⟨O, hO, h1O, hOs⟩ := mem_nhdsWithin.1 hne'
  have h𝒰 : IsOpenFieldSet PeriodicLattice.compactGaugeGroup ((O ∩ O₀) ∩ fieldSpace L n k j) :=
    (hop _).2 ⟨inter_subset_right, O ∩ O₀, hO.inter hO₀, rfl⟩
  have hsub : (O ∩ O₀) ∩ fieldSpace L n k j ⊆ 𝒰₀ := fun V hV => by
    rw [e₀]
    exact ⟨hV.1.2, hV.2⟩
  have h2 : trivialField L n k j ∈ O₀ ∩ fieldSpace L n k j := by
    rw [← e₀]
    exact h.2
  exact ⟨_, ⟨h𝒰, ⟨⟨h1O, h2.1⟩, h2.2⟩⟩, hsub, fun V hV => hOs ⟨hV.1.1, hV.2⟩⟩
end Sets
section Near
variable {L n k : ℕ}
structure StepLinear (L n k i : ℕ) (V : Edge L n k i → ComplexMatrix2) : Prop where
  differential : ∃ T : edgeFormSpace L n k i →ₗ[ℝ] edgeFormSpace L n k (i + 1), ∀ B : edgeFormSpace L n k i,
    (T B : Edge L n k (i + 1) → ComplexMatrix2) = complexSmoothingDeriv V (B : Edge L n k i → ComplexMatrix2)
  drift : ∃ T : edgeFormSpace L n k i →ₗ[ℝ] vertexFunctionSpace L n k (i + 1), ∀ B : edgeFormSpace L n k i,
    (T B : Vertex L n k (i + 1) → ComplexMatrix2) = contourLogDrift V (B : Edge L n k i → ComplexMatrix2)
  average : ∃ T : vertexFunctionSpace L n k i →ₗ[ℝ] vertexFunctionSpace L n k (i + 1),
    ∀ l : vertexFunctionSpace L n k i,
    (T l : Vertex L n k (i + 1) → ComplexMatrix2) = adjointCubeAverage V (l : Vertex L n k i → ComplexMatrix2)
structure IteratesReal (L n k j : ℕ) (U : Edge L n k 0 → ComplexMatrix2) : Prop where
  covariant : ∀ B : edgeFormSpace L n k 0,
    iterCovariantDeriv L n k U j (B : Edge L n k 0 → ComplexMatrix2) ∈ edgeFormSpace L n k j
  differential : ∀ B : edgeFormSpace L n k 0,
    complexIterDeriv L n k j U (B : Edge L n k 0 → ComplexMatrix2) ∈ edgeFormSpace L n k j
  drift : ∀ B : edgeFormSpace L n k 0,
    iterContourLogDrift L n k U j (B : Edge L n k 0 → ComplexMatrix2) ∈ vertexFunctionSpace L n k j
  average : ∀ l : vertexFunctionSpace L n k 0,
    iterAdjointCubeAverage L n k U j (l : Vertex L n k 0 → ComplexMatrix2) ∈ vertexFunctionSpace L n k j
structure NearIdentityFacts (L n k : ℕ) (U : Edge L n k 0 → ComplexMatrix2) : Prop where
  small : U ∈ smallIterateFields L n k
  iterate_eq : ∀ i ≤ k, PeriodicLattice.complexBlockFieldAtLevel i U = smoothingIter L n k i U
  configuration : ∀ i ≤ k, smoothingIter L n k i U ∈ fieldSpace L n k i
  step : ∀ i < k, StepLinear L n k i (PeriodicLattice.complexBlockFieldAtLevel i U)
  real : ∀ i ≤ k, IteratesReal L n k i U
theorem mem_fieldsIn_complex {j : ℕ} {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j) :
    V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_fieldsIn_of_mem <;> assumption
theorem mem_complexEdgeForms {j : ℕ} {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j) :
    B ∈ complexEdgeForms L n k j := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_complexEdgeForms_of_mem <;> assumption
theorem complexBlockField_eq_of_meanSequence (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) {W : Edge L n k 0 → ComplexMatrix2} {Vf : ∀ i : ℕ, Edge L n k i → ComplexMatrix2}
    (h : LevelwiseMeans.IsMeanSequence k Vf) (h0 : Vf 0 = W) :
    ∀ i, i ≤ k → PeriodicLattice.complexBlockFieldAtLevel i W = Vf i := by
  have hO := (G.formed L hL k hk).1 n hn
  intro i
  induction i with
  | zero => exact fun _ => h0.symm
  | succ i ih =>
    intro hi
    have hi' : i < k := hi
    have e := ih hi'.le
    have hu := (hO.meanStep_unique i hi' (Vf i) ⟨h.mem_fields i hi'.le, h.norm_sub_one_lt i hi'⟩
      (Vf (i + 1)) (h.mem_fields (i + 1) hi)).1 (fun c hc => h.eq_mean i hi' c hc)
    show PeriodicLattice.complexBlockAverageStep i (PeriodicLattice.complexBlockFieldAtLevel i W) = Vf (i + 1)
    rw [e, hu]
    rfl
theorem eventually_nearIdentityFacts (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) :
    EventuallyNearIdentity (fieldSpace L n k 0) (NearIdentityFacts L n k) := by
  classical
  have hH := (G.levels L hL k hk).1 n hn
  have hAt := (G.linear L n k hL hn hk).1
  have hstep : ∀ᶠ U in 𝓝[fieldSpace L n k 0] (fun _ => (1 : ComplexMatrix2)),
      ∀ i ∈ Finset.range k, StepLinear L n k i (smoothingIter L n k i U) := by
    refine (Finset.eventually_all _).2 fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    have t := hH.iterate_tendsto i hi'.le
    filter_upwards [t.eventually (hAt i hi').complexSmoothingDeriv_isLinear,
      t.eventually (hAt i hi').contourLogDrift_isLinear,
      t.eventually (hAt i hi').adjointCubeAverage_isLinear] with U b₁ b₂ b₃
    exact ⟨b₁, b₂, b₃⟩
  have hreal : ∀ᶠ U in 𝓝[fieldSpace L n k 0] (fun _ => (1 : ComplexMatrix2)),
      ∀ i ∈ Finset.range k, IteratesReal L n k (i + 1) U := by
    refine (Finset.eventually_all _).2 fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    filter_upwards [(hAt i hi').iterCovariantDeriv_isLinear,
      (hAt i hi').complexIterDeriv_isLinear,
      (hAt i hi').iterContourLogDrift_isLinear,
      (hAt i hi').iterAdjointCubeAverage_isLinear] with U b₁ b₂ b₃ b₄
    obtain ⟨T₁, h₁⟩ := b₁
    obtain ⟨T₂, h₂⟩ := b₂
    obtain ⟨T₃, h₃⟩ := b₃
    obtain ⟨T₄, h₄⟩ := b₄
    exact ⟨fun B => h₁ B ▸ (T₁ B).2, fun B => h₂ B ▸ (T₂ B).2, fun B => h₃ B ▸ (T₃ B).2,
      fun l => h₄ l ▸ (T₄ l).2⟩
  have hformed : ∀ᶠ U in 𝓝[fieldSpace L n k 0] (fun _ => (1 : ComplexMatrix2)), _ :=
    hH.iterates_defined
  filter_upwards [hformed, self_mem_nhdsWithin, hstep, hreal] with U hU hUc₀ hs hr
  let Vf : ∀ i : ℕ, Edge L n k i → ComplexMatrix2 := fun i => smoothingIter L n k i U
  have hfam : LevelwiseMeans.IsMeanSequence k Vf := by
    refine ⟨fun i hi => mem_fieldsIn_complex (hU i hi).1, fun i hi b => (hU i hi.le).2.1 b,
      fun i hi c hc => ?_⟩
    have e := (hU (i + 1) hi).2.2.1 c
    have e0 : LevelwiseMeans.levelwiseMean U i = fun c => some (Vf i c) :=
      funext (hU i hi.le).2.2.1
    rw [LevelwiseMeans.levelwiseMean] at e
    simp only [if_pos hc] at e
    rw [e0] at e
    unfold LevelwiseMeans.meanOfDefined at e
    split_ifs at e
    exact (Option.some.inj e).symm
  have heq : ∀ i, i ≤ k → PeriodicLattice.complexBlockFieldAtLevel i U = Vf i :=
    complexBlockField_eq_of_meanSequence G hL hn hk hfam rfl
  have hsmall : U ∈ smallIterateFields L n k :=
    ⟨mem_fieldsIn_complex hUc₀, fun j hj => by
      rw [heq j hj.le]
      exact ⟨mem_fieldsIn_complex (hU j hj.le).1, (hU j hj.le).2.1⟩⟩
  refine ⟨hsmall, heq, fun i hi => (hU i hi).1, fun i hi => ?_, fun i hi => ?_⟩
  · rw [heq i hi.le]
    exact hs i (Finset.mem_range.2 hi)
  · cases i with
    | zero =>
      refine ⟨fun B => B.2, fun B => ?_, fun B => (vertexFunctionSpace L n k 0).zero_mem, fun l => l.2⟩
      rw [(G.chain L hL n k hn U hsmall B.1 (mem_complexEdgeForms B.2)).1]
      exact B.2
    | succ i => exact hr i (Finset.mem_range.2 hi)
theorem exists_pullback_along_iter (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ} (hj : j ≤ k) {𝒰₀ : Set (Edge L n k 0 → ComplexMatrix2)}
    (h₀ : IsOpenNhdOfOne 𝒰₀) (hf : ∀ U ∈ 𝒰₀, NearIdentityFacts L n k U)
    {𝒰' : Set (Edge L n k j → ComplexMatrix2)} (h' : IsOpenNhdOfOne 𝒰') :
    ∃ 𝒲 : Set (Edge L n k 0 → ComplexMatrix2), IsOpenNhdOfOne 𝒲 ∧ 𝒲 ⊆ 𝒰₀ ∧
      ∀ F : (Edge L n k j → ComplexMatrix2) → ℝ, IsAnalyticFieldFunction 𝒰' F →
        IsAnalyticFieldFunction 𝒲 fun U => F (PeriodicLattice.complexBlockFieldAtLevel j U) := by
  cases j with
  | zero =>
    obtain ⟨𝒲, h𝒲, hs, hm⟩ := exists_open_of_eventually G hL hn (Nat.zero_le k) h₀
      (eventuallyNearIdentity_mem G hL hn (Nat.zero_le k) h')
    obtain ⟨-, -, hmono, -, -⟩ := G.algebra L n k 0 0 hL hn (Nat.zero_le k) (Nat.zero_le k)
    exact ⟨𝒲, h𝒲, hs, fun F hF => hmono _ _ F hF h𝒲.1 hm⟩
  | succ i =>
    obtain ⟨𝒰m, hm, hM, -⟩ := G.iterate L n k i hL hn hj
    obtain ⟨-, -, hmono, hcongr, hcomp⟩ := G.algebra L n k 0 (i + 1) hL hn (Nat.zero_le k) hj
    have hc0 := (G.algebra L n k (i + 1) (i + 1) hL hn hj hj).1 𝒰' 0 h'.1
    have h1 : smoothingIter L n k (i + 1) (trivialField L n k 0) ∈ 𝒰' :=
      (((G.levels L hL k hk).1 n hn).iterate_tendsto (i + 1) hj).eventually
        (eventuallyNearIdentity_mem G hL hn hj h') |>.self_of_nhdsWithin trivialField_mem_fieldSpace
    have hS : IsOpenNhdOfOne (𝒰m ∩ smoothingIter L n k (i + 1) ⁻¹' 𝒰') :=
      ⟨(hcomp _ _ _ _ hM hc0).1, hm.2, h1⟩
    obtain ⟨𝒲, h𝒲, hs, hm'⟩ := exists_open_of_eventually G hL hn (Nat.zero_le k) h₀
      (eventuallyNearIdentity_mem G hL hn (Nat.zero_le k) hS)
    refine ⟨𝒲, h𝒲, hs, fun F hF => hcongr _ _ _ (hmono _ _ _ (hcomp _ _ _ _ hM hF) h𝒲.1 hm')
      fun U hU => ?_⟩
    show F (smoothingIter L n k (i + 1) U) = F (PeriodicLattice.complexBlockFieldAtLevel (i + 1) U)
    rw [(hf U (hs hU)).iterate_eq (i + 1) hj]
structure AnalyticEntries (L n k : ℕ) (𝒰 : Set (Edge L n k 0 → ComplexMatrix2)) (j : ℕ) : Prop where
  covariant : ∀ (B : edgeFormSpace L n k 0) (c : PositiveEdge L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
    IsAnalyticFieldFunction 𝒰 fun U =>
      φ (iterCovariantDeriv L n k U j (B : Edge L n k 0 → ComplexMatrix2) c.1)
  differential : ∀ (B : edgeFormSpace L n k 0) (c : PositiveEdge L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
    IsAnalyticFieldFunction 𝒰 fun U =>
      φ (complexIterDeriv L n k j U (B : Edge L n k 0 → ComplexMatrix2) c.1)
  drift : ∀ (B : edgeFormSpace L n k 0) (y : Vertex L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
    IsAnalyticFieldFunction 𝒰 fun U =>
      φ (iterContourLogDrift L n k U j (B : Edge L n k 0 → ComplexMatrix2) y)
  average : ∀ (l : vertexFunctionSpace L n k 0) (y : Vertex L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
    IsAnalyticFieldFunction 𝒰 fun U =>
      φ (iterAdjointCubeAverage L n k U j (l : Vertex L n k 0 → ComplexMatrix2) y)
theorem analyticAlgebra (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {𝒰 : Set (Edge L n k 0 → ComplexMatrix2)} (hop : IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰) :
    AnalyticAlgebra 𝒰 := by
  obtain ⟨hconst, hsp, -, hcongr, -⟩ := G.algebra L n k 0 0 hL hn (Nat.zero_le k) (Nat.zero_le k)
  exact ⟨fun c => hconst 𝒰 c hop, fun h₁ h₂ => (hsp _ _ _ h₁ h₂).1, fun h₁ h₂ => (hsp _ _ _ h₁ h₂).2,
    fun h₁ h₂ => hcongr _ _ _ h₁ h₂⟩
theorem analyticEntries_succ (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hk : 1 ≤ k) {j : ℕ} (hj : j + 1 ≤ k) {𝒰₁ : Set (Edge L n k 0 → ComplexMatrix2)}
    (h₁ : IsOpenNhdOfOne 𝒰₁) (hf : ∀ U ∈ 𝒰₁, NearIdentityFacts L n k U)
    (E : AnalyticEntries L n k 𝒰₁ j) :
    ∃ 𝒲 : Set (Edge L n k 0 → ComplexMatrix2), IsOpenNhdOfOne 𝒲 ∧ 𝒲 ⊆ 𝒰₁ ∧
      AnalyticEntries L n k 𝒲 (j + 1) := by
  have hj' : j < k := hj
  obtain ⟨𝒰s, hs, hQ, hN, hA⟩ := G.step L n k j hL hn hj'
  obtain ⟨𝒲₁, hW₁, hs₁, pb₁⟩ := exists_pullback_along_iter G hL hn hk hj'.le h₁ hf hs
  obtain ⟨𝒲, hW, hs₂, pb₂⟩ := exists_pullback_along_iter G hL hn hk hj hW₁
    (fun U hU => hf U (hs₁ hU)) (fieldSpace_isOpenNhdOfOne G hL hn hj)
  have hsub : 𝒲 ⊆ 𝒰₁ := hs₂.trans hs₁
  have hF : ∀ U ∈ 𝒲, NearIdentityFacts L n k U := fun U hU => hf U (hsub hU)
  have hop := hW.1
  have alg := analyticAlgebra G hL hn hop
  obtain ⟨-, -, hmono, -, -⟩ := G.algebra L n k 0 0 hL hn (Nat.zero_le k) (Nat.zero_le k)
  have hc0 := (G.algebra L n k (j + 1) (j + 1) hL hn hj hj).1 (fieldSpace L n k (j + 1)) 0
    (fieldSpace_isOpenNhdOfOne G hL hn hj).1
  have hDiff := (G.linear L n k hL hn hk).2.covDiff_isLinear
  have appQ : ∀ (Y : (Edge L n k 0 → ComplexMatrix2) → Edge L n k j → ComplexMatrix2),
      (∀ (c : PositiveEdge L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
        IsAnalyticFieldFunction 𝒲 fun U => φ (Y U c.1)) →
      (∀ U ∈ 𝒲, Y U ∈ edgeFormSpace L n k j) →
      ∀ (c : PositiveEdge L n k (j + 1)) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ), IsAnalyticFieldFunction 𝒲 fun U =>
        φ (complexSmoothingDeriv (PeriodicLattice.complexBlockFieldAtLevel j U) (Y U) c.1) := by
    intro Y hY hm c φ
    refine analytic_at_edgeForm G hL hn hj'.le alg
      (H := fun U w => complexSmoothingDeriv (PeriodicLattice.complexBlockFieldAtLevel j U) w c.1)
      (fun U hU => ?_) (fun w ψ => ?_) hY hm φ
    · obtain ⟨T, hT⟩ := ((hF U hU).step j hj').differential
      exact ⟨LinearMap.proj c.1 ∘ₗ (edgeFormSpace L n k (j + 1)).subtype ∘ₗ T, fun w => by
        simp [hT]⟩
    · exact hmono _ _ _ (pb₁ _ (hQ w c ψ)) hop hs₂
  have appN : ∀ (Y : (Edge L n k 0 → ComplexMatrix2) → Edge L n k j → ComplexMatrix2),
      (∀ (c : PositiveEdge L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
        IsAnalyticFieldFunction 𝒲 fun U => φ (Y U c.1)) →
      (∀ U ∈ 𝒲, Y U ∈ edgeFormSpace L n k j) →
      ∀ (y : Vertex L n k (j + 1)) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ), IsAnalyticFieldFunction 𝒲 fun U =>
        φ (contourLogDrift (PeriodicLattice.complexBlockFieldAtLevel j U) (Y U) y) := by
    intro Y hY hm y φ
    refine analytic_at_edgeForm G hL hn hj'.le alg
      (H := fun U w => contourLogDrift (PeriodicLattice.complexBlockFieldAtLevel j U) w y)
      (fun U hU => ?_) (fun w ψ => ?_) hY hm φ
    · obtain ⟨T, hT⟩ := ((hF U hU).step j hj').drift
      exact ⟨LinearMap.proj y ∘ₗ (vertexFunctionSpace L n k (j + 1)).subtype ∘ₗ T, fun w => by
        simp [hT]⟩
    · exact hmono _ _ _ (pb₁ _ (hN w y ψ)) hop hs₂
  have appA : ∀ (Y : (Edge L n k 0 → ComplexMatrix2) → Vertex L n k j → ComplexMatrix2),
      (∀ (x : Vertex L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
        IsAnalyticFieldFunction 𝒲 fun U => φ (Y U x)) →
      (∀ U ∈ 𝒲, Y U ∈ vertexFunctionSpace L n k j) →
      ∀ (y : Vertex L n k (j + 1)) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ), IsAnalyticFieldFunction 𝒲 fun U =>
        φ (adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j U) (Y U) y) := by
    intro Y hY hm y φ
    refine analytic_at_vertexFunction G hL hn hj'.le alg
      (H := fun U w => adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j U) w y)
      (fun U hU => ?_) (fun w ψ => ?_) hY hm φ
    · obtain ⟨T, hT⟩ := ((hF U hU).step j hj').average
      exact ⟨LinearMap.proj y ∘ₗ (vertexFunctionSpace L n k (j + 1)).subtype ∘ₗ T, fun w => by
        simp [hT]⟩
    · exact hmono _ _ _ (pb₁ _ (hA w y ψ)) hop hs₂
  have appD : ∀ (Y : (Edge L n k 0 → ComplexMatrix2) → Vertex L n k (j + 1) → ComplexMatrix2),
      (∀ (x : Vertex L n k (j + 1)) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
        IsAnalyticFieldFunction 𝒲 fun U => φ (Y U x)) →
      (∀ U ∈ 𝒲, Y U ∈ vertexFunctionSpace L n k (j + 1)) →
      ∀ (c : PositiveEdge L n k (j + 1)) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ), IsAnalyticFieldFunction 𝒲 fun U =>
        φ (covDiff (PeriodicLattice.complexBlockFieldAtLevel (j + 1) U) (Y U) c.1) := by
    intro Y hY hm c φ
    refine analytic_at_vertexFunction G hL hn hj alg
      (H := fun U w => covDiff (PeriodicLattice.complexBlockFieldAtLevel (j + 1) U) w c.1)
      (fun U hU => ?_) (fun w ψ => ?_) hY hm φ
    · have hc : PeriodicLattice.complexBlockFieldAtLevel (j + 1) U ∈ fieldSpace L n k (j + 1) := by
        rw [(hF U hU).iterate_eq (j + 1) hj]
        exact (hF U hU).configuration (j + 1) hj
      obtain ⟨T, hT⟩ := hDiff (j + 1) hj _ hc
      exact ⟨LinearMap.proj c.1 ∘ₗ (edgeFormSpace L n k (j + 1)).subtype ∘ₗ T, fun w => by
        simp [hT]⟩
    · exact pb₂ _ (covDiff_entries_analytic G.holomorphy hc0 w c ψ)
  have eC : ∀ (B : edgeFormSpace L n k 0) (c : PositiveEdge L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
      IsAnalyticFieldFunction 𝒲 fun U =>
        φ (iterCovariantDeriv L n k U j (B : Edge L n k 0 → ComplexMatrix2) c.1) :=
    fun B c φ => hmono _ _ _ (E.covariant B c φ) hop hsub
  have eD : ∀ (B : edgeFormSpace L n k 0) (c : PositiveEdge L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
      IsAnalyticFieldFunction 𝒲 fun U =>
        φ (complexIterDeriv L n k j U (B : Edge L n k 0 → ComplexMatrix2) c.1) :=
    fun B c φ => hmono _ _ _ (E.differential B c φ) hop hsub
  have eN : ∀ (B : edgeFormSpace L n k 0) (y : Vertex L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
      IsAnalyticFieldFunction 𝒲 fun U =>
        φ (iterContourLogDrift L n k U j (B : Edge L n k 0 → ComplexMatrix2) y) :=
    fun B y φ => hmono _ _ _ (E.drift B y φ) hop hsub
  have eA : ∀ (l : vertexFunctionSpace L n k 0) (y : Vertex L n k j) (φ : ComplexMatrix2 →ₗ[ℝ] ℝ),
      IsAnalyticFieldFunction 𝒲 fun U =>
        φ (iterAdjointCubeAverage L n k U j (l : Vertex L n k 0 → ComplexMatrix2) y) :=
    fun l y φ => hmono _ _ _ (E.average l y φ) hop hsub
  have mC := fun (B : edgeFormSpace L n k 0) U (hU : U ∈ 𝒲) => ((hF U hU).real j hj'.le).covariant B
  have mD := fun (B : edgeFormSpace L n k 0) U (hU : U ∈ 𝒲) => ((hF U hU).real j hj'.le).differential B
  have mN := fun (B : edgeFormSpace L n k 0) U (hU : U ∈ 𝒲) => ((hF U hU).real j hj'.le).drift B
  have mA := fun (l : vertexFunctionSpace L n k 0) U (hU : U ∈ 𝒲) => ((hF U hU).real j hj'.le).average l
  refine ⟨𝒲, hW, hsub, fun B c φ => ?_, fun B c φ => ?_, fun B y φ => ?_, fun l y φ => ?_⟩
  · have hmem : ∀ U ∈ 𝒲, contourLogDrift (PeriodicLattice.complexBlockFieldAtLevel j U)
        (iterCovariantDeriv L n k U j (B : Edge L n k 0 → ComplexMatrix2)) ∈
          vertexFunctionSpace L n k (j + 1) := by
      intro U hU
      obtain ⟨T, hT⟩ := ((hF U hU).step j hj').drift
      exact hT ⟨_, mC B U hU⟩ ▸ (T ⟨_, mC B U hU⟩).2
    exact alg.congr (alg.add (appQ _ (eC B) (mC B) c φ)
      (appD _ (appN _ (eC B) (mC B)) hmem c φ)) fun U _ => (map_add φ _ _).symm
  · refine alg.congr (appQ _ (eD B) (mD B) c φ) fun U hU => ?_
    show _ = φ (complexIterDeriv L n k (j + 1) U (B : Edge L n k 0 → ComplexMatrix2) c.1)
    rw [((G.chain L hL n k hn U (hF U hU).small B.1 (mem_complexEdgeForms B.2)).2.1 j hj')]
  · exact alg.congr (alg.add (appA _ (eN B) (mN B) y φ) (appN _ (eD B) (mD B) y φ))
      fun U _ => (map_add φ _ _).symm
  · exact appA _ (eA l) (mA l) y φ
end Near
end CovariantIterates
open CovariantIterates in
theorem CovariantIterates.proof
    (hStep : SmoothingStepAnalyticEntries)
    (hIter : SmoothingIterAnalyticNearOne)
    (hAlg : AnalyticFieldFunctionsClosed)
    (hBonds : BondSetFields.ProductStructureHolds)
    (hSpaces : FiniteSideFormSpaces)
    (hSums : FaceSums.FacesAndPairings)
    (hLinear : RealLinearMaps.RealLinearMapsStatement)
    (hLevels : LevelwiseMeans.LevelwiseMeansHold)
    (hFormed : IteratedMeans.IteratedMeansHold)
    (hChain : ComplexIterDerivChain)
    (hHol : HolomorphyClosureStatement) :
    CovariantIteratesAnalyticEntries := by
  intro L n k j hL hn hk hj
  have G : Inputs := ⟨hStep, hIter, hAlg, hBonds, hSpaces, hSums, hLinear, hLevels, hFormed, hChain,
    hHol⟩
  obtain ⟨𝒰₀, h₀, -, hf⟩ := exists_open_of_eventually G hL hn (Nat.zero_le k)
    (fieldSpace_isOpenNhdOfOne G hL hn (Nat.zero_le k)) (eventually_nearIdentityFacts G hL hn hk)
  have key : ∀ j, j ≤ k → ∃ 𝒰 : Set (Edge L n k 0 → ComplexMatrix2), IsOpenNhdOfOne 𝒰 ∧
      𝒰 ⊆ 𝒰₀ ∧ AnalyticEntries L n k 𝒰 j := by
    intro j
    induction j with
    | zero =>
      intro _
      have alg := analyticAlgebra G hL hn h₀.1
      refine ⟨𝒰₀, h₀, subset_rfl,
        fun B c φ => alg.congr (alg.const (φ ((B : Edge L n k 0 → ComplexMatrix2) c.1))) fun U _ => rfl,
        fun B c φ => ?_, fun B y φ => ?_,
        fun l y φ => alg.congr (alg.const (φ ((l : Vertex L n k 0 → ComplexMatrix2) y))) fun U _ => rfl⟩
      · refine alg.congr (alg.const (φ ((B : Edge L n k 0 → ComplexMatrix2) c.1))) fun U hU => ?_
        show _ = φ (complexIterDeriv L n k 0 U (B : Edge L n k 0 → ComplexMatrix2) c.1)
        rw [(hChain L hL n k hn U (hf U hU).small B.1 (mem_complexEdgeForms B.2)).1]
      · refine alg.congr (alg.const 0) fun U _ => ?_
        simp [iterContourLogDrift]
    | succ j ih =>
      intro hj
      obtain ⟨𝒰, h, hs, E⟩ := ih (Nat.le_of_succ_le hj)
      obtain ⟨𝒲, hW, hs', E'⟩ := analyticEntries_succ G hL hn hk hj h (fun U hU => hf U (hs hU)) E
      exact ⟨𝒲, hW, hs'.trans hs, E'⟩
  obtain ⟨𝒰, h, -, E⟩ := key j hj
  exact ⟨𝒰, h, E.covariant, E.drift, E.average⟩
end YangMills.Construction
end
