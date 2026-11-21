import YangMills.Construction.Towers.IteratedAveragesReadOnlyTheBlocksAtTheSideInfinityProof
import YangMills.Construction.Towers.BondsOnWhichTheAveragesDepend
import YangMills.Construction.Towers.CovariantAveragesAsDifferentials
import Mathlib
import YangMills.Construction.Towers.RelationsOfTheCovariantIteratesOfTheWholeLatticeProof
import YangMills.Construction.Towers.SecondOrderTermAtTheSideInfinityIsLocalProof
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ReadsCubes
open _root_.YangMills.Construction.Tower.SupportOfMeans.Unbounded (supportEdges)
open _root_.YangMills.Construction.Tower.FullSpace.AsDifferentials (complexQuadraticTerm)
variable {L k : ℕ}
def cubeVertices (y : Vertex L k k) : Set (Vertex L k 0) :=
  {x | (x : InfiniteLattice.AmbientSpace) ∈ cubeOfOrder L (meshAt L k 0) k y}
def cubePositiveEdges (y : Vertex L k k) : Set (Edge L k 0) :=
  {b | b.IsPositivelyOriented ∧ b.initial ∈ cubeVertices y ∧ b.terminal ∈ cubeVertices y}
def IsFinitelySupportedForm (B : Edge L k 0 → Matrices.ComplexMatrix2) : Prop :=
  B ∈ complexEdgeForms (meshAt L k 0) ∧ HasFiniteSupp (restrictToPositiveEdges B)
structure LocalAt (U : Edge L k 0 → Matrices.ComplexMatrix2) : Prop where
  iterCovariantDeriv_local : ∀ (c : PositiveEdge (meshAt L k k))
    (B B' : Edge L k 0 → Matrices.ComplexMatrix2),
    IsFinitelySupportedForm B → IsFinitelySupportedForm B' → (∀ b ∈ supportEdges c.1, B b = B' b) →
      iterCovariantDeriv L k U k B c.1 = iterCovariantDeriv L k U k B' c.1
  quadraticTerm_local : ∀ (c : PositiveEdge (meshAt L k k))
    (B₁ B₁' B₂ B₂' : Edge L k 0 → Matrices.ComplexMatrix2),
    IsFinitelySupportedForm B₁ → IsFinitelySupportedForm B₁' → IsFinitelySupportedForm B₂ →
      IsFinitelySupportedForm B₂' → (∀ b ∈ supportEdges c.1, B₁ b = B₁' b ∧ B₂ b = B₂' b) →
        complexQuadraticTerm L k U B₁ B₂ c = complexQuadraticTerm L k U B₁' B₂' c
  contourDrift_local : ∀ (y : Vertex L k k) (B B' : Edge L k 0 → Matrices.ComplexMatrix2),
    IsFinitelySupportedForm B → IsFinitelySupportedForm B' → (∀ b ∈ cubePositiveEdges y, B b = B' b) →
      iterContourLogDrift L k U k B y = iterContourLogDrift L k U k B' y
  cubeAverage_local : ∀ (y : Vertex L k k) (l l' : Vertex L k 0 → Matrices.ComplexMatrix2),
    (∀ x ∈ cubeVertices y, l x = l' x) →
      iterAdjointCubeAverage L k U k l y = iterAdjointCubeAverage L k U k l' y
  iterCovariantDeriv_finiteSupp : ∀ B : Edge L k 0 → Matrices.ComplexMatrix2,
    IsFinitelySupportedForm B →
      HasFiniteSupp (restrictToPositiveEdges (iterCovariantDeriv L k U k B))
  quadraticTerm_finiteSupp : ∀ B B' : Edge L k 0 → Matrices.ComplexMatrix2,
    IsFinitelySupportedForm B → IsFinitelySupportedForm B' →
      HasFiniteSupp (complexQuadraticTerm L k U B B')
  contourDrift_finiteSupp : ∀ B : Edge L k 0 → Matrices.ComplexMatrix2,
    IsFinitelySupportedForm B → HasFiniteSupp (iterContourLogDrift L k U k B)
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ U ∈ smallIterateFields L k, LocalAt U) ∧
    (∀ b : Edge L k 0,
      {c : Edge L k k | c.IsPositivelyOriented ∧ b ∈ supportEdges c}.encard ≤ 8) ∧
    ∀ b : Edge L k 0, {y : Vertex L k k | b ∈ cubePositiveEdges y}.encard ≤ 1
end YangMills.Construction.Tower.FullSpace.ReadsCubes
end

open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ReadsCubes
open YangMills.Construction.Tower.SupportOfMeans (DefinedAlike DependsOnlyOn)
open YangMills.Construction.Tower.SupportOfMeans.Unbounded (baseFields endpointBlocks
  supportEdges HasEndpointsIn meanAt)
open YangMills.Construction.Tower.AsDifferentials (boundedSubmodule quadraticTermAt
  HasUniqueQuadraticTerm HasDerivAtZeroAlong)
open YangMills.Construction.Tower.FullSpace.AsDifferentials (complexQuadraticTerm iterRatio
  iterMean topDeriv topLogRatio)
section SingleLattice
variable {a a' : ℝ}
theorem opposite_isPositivelyOriented_of_not {v : InfiniteLattice.Link a}
    (h : ¬v.IsPositivelyOriented) : v.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem expTwist_congr {C C' V : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    {v : InfiniteLattice.Link a}
    (h₁ : v.IsPositivelyOriented → C v = C' v)
    (h₂ : ¬v.IsPositivelyOriented → C v.opposite = C' v.opposite) :
    expTwist C V v = expTwist C' V v := by
  by_cases hv : v.IsPositivelyOriented
  · simp [expTwist, hv, h₁ hv]
  · simp [expTwist, hv, h₂ hv]
theorem complexContourMean_congr (L : ℕ) {W W' : InfiniteLattice.Link a' → Matrices.ComplexMatrix2}
    {y : InfiniteLattice.LatticePoint a} {x : InfiniteLattice.LatticePoint a'}
    (h : ∀ σ, ∀ v ∈ contour L y x σ, W v = W' v) :
    complexContourMean L W y x = complexContourMean L W' y x := by
  have e : contourHolonomies L W y x = contourHolonomies L W' y x := by
    funext σ
    simp only [contourHolonomies, linkHolonomy]
    rw [List.map_congr_left (h σ)]
  simp only [complexContourMean, e]
theorem covDiff_of_isPositivelyOriented (V : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (l : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2) {c : InfiniteLattice.Link a}
    (hc : c.IsPositivelyOriented) :
    covDiff V l c = Matrices.ComplexMatrix2.conjugateBy (V c) (l c.terminal) - l c.initial := by
  simp [covDiff, extendOddly, hc]
theorem covDiff_zero (V : InfiniteLattice.Link a → Matrices.ComplexMatrix2) :
    covDiff V (0 : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.CovariantIterRelationsProof.covDiff_zero <;> assumption
theorem hasFiniteSupp_of_vanishing {ι β : Type*} {S : Set β} (hS : S.Finite) (R : ι → Set β)
    (hR : ∀ v ∈ S, {i | v ∈ R i}.Finite) {g : ι → Matrices.ComplexMatrix2}
    (h : ∀ i, (∀ v ∈ R i, v ∉ S) → g i = 0) :
    HasFiniteSupp g := by
  refine (hS.biUnion hR).subset fun i hi => ?_
  by_contra hno
  apply hi
  refine h i fun v hv hvS => hno ?_
  exact mem_iUnion₂.2 ⟨v, hvS, hv⟩
end SingleLattice
variable {L k : ℕ}
def verticesOfOrder (j : ℕ) (y : Vertex L k j) : Set (Vertex L k 0) :=
  {x | (x : InfiniteLattice.AmbientSpace) ∈ cubeOfOrder L (meshAt L k 0) j y}
def edgesOfOrder (j : ℕ) (y : Vertex L k j) : Set (Edge L k 0) :=
  {v | v.IsPositivelyOriented ∧ v.initial ∈ verticesOfOrder j y ∧ v.terminal ∈ verticesOfOrder j y}
theorem mem_verticesOfOrder_zero (y : Vertex L k 0) : y ∈ verticesOfOrder 0 y :=
  ⟨0, by simp, by simp⟩
theorem verticesOfOrder_subset_succ (h₄ : Tower.BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {j : ℕ} (hj : j < k)
    {y : Vertex L k (j + 1)} {x : Vertex L k j}
    (hx : (x : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y) :
    verticesOfOrder j x ⊆ verticesOfOrder (j + 1) y := by
  intro z hz
  have H := (h₄ L hL k (j + 1) (j + 1) hk le_rfl (by omega)).2.1.eq_biUnion_lower (by omega) y
  rw [Nat.sub_self] at H
  change (z : InfiniteLattice.AmbientSpace) ∈ cubeOfOrder L (meshAt L k 0) (j + 1) y
  rw [H]
  exact mem_iUnion₂.2 ⟨x, hx, hz⟩
theorem contour_endpoints_mem_cube (h₄ : Tower.BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {j : ℕ} (hj : j < k)
    {y : Vertex L k (j + 1)} {x : Vertex L k j}
    (hx : x ∈ FullSpace.cubeVertices L (meshAt L k j) y)
    (σ : ContourOrder L y x) {v : Edge L k j} (hv : v ∈ contour L y x σ) :
    (v.initial : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y ∧
      (v.terminal : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y := by apply _root_.YangMills.Construction.Tower.FullSpace.IterLocality.contour_endpoints_mem_cube <;> assumption
theorem contourLogDrift_congr (h₄ : Tower.BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {j : ℕ} (hj : j < k)
    (V C C' : Edge L k j → Matrices.ComplexMatrix2) (y : Vertex L k (j + 1))
    (h : ∀ v : Edge L k j, v.IsPositivelyOriented →
      (v.initial : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y →
      (v.terminal : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y → C v = C' v) :
    contourLogDrift V C y = contourLogDrift V C' y := by
  simp only [contourLogDrift]
  refine congrArg _ (finsum_mem_congr rfl fun x hx => ?_)
  have key : ∀ t : ℂ, complexContourMean L (expTwist (algebraMap ℂ ℂ t • C) V) y x =
      complexContourMean L (expTwist (algebraMap ℂ ℂ t • C') V) y x := by
    intro t
    refine complexContourMean_congr L fun σ v hv => ?_
    obtain ⟨ht, hh⟩ := contour_endpoints_mem_cube h₄ hL hk hj hx σ hv
    refine expTwist_congr (fun hp => ?_) fun hp => ?_
    · simp [h v hp ht hh]
    · simp [h v.opposite (opposite_isPositivelyOriented_of_not hp) hh ht]
  simp only [logDirectionalDeriv, key]
theorem getD_eq_of_definedAlike {p q : Option Matrices.ComplexMatrix2} (h : DefinedAlike p q) :
    p.getD 1 = q.getD 1 := by apply _root_.YangMills.Construction.LocalKernels.QuadraticLocality.getD_eq_of_definedAlike <;> assumption
theorem iterLogRatio_congr {j : ℕ} {F : Finset (Edge L k 0)} {c : Edge L k j}
    (hR : DependsOnlyOn (baseFields L k) F (fun v => v.IsPositivelyOriented) expTwist
      (meanAt c))
    {W : Edge L k 0 → Matrices.ComplexMatrix2} (hW : W ∈ baseFields L k)
    {C C' : Edge L k 0 → Matrices.ComplexMatrix2} (hC : C ∈ complexEdgeForms (meshAt L k 0))
    (hC' : C' ∈ complexEdgeForms (meshAt L k 0)) (h : ∀ v ∈ F, C v = C' v) :
    FullSpace.AsDifferentials.iterLogRatio W j c C =
      FullSpace.AsDifferentials.iterLogRatio W j c C' := by
  have h₁ : IsEdgeFormIn PeriodicLattice.complexLieAlgebra C := hC
  have h₂ : IsEdgeFormIn PeriodicLattice.complexLieAlgebra C' := hC'
  have e := getD_eq_of_definedAlike
    (hR.definedAlike_twist W hW W hW C C' h₁.1 h₂.1 fun v hv => ⟨rfl, h v hv⟩)
  have e' : iterMean (expTwist C W) j c = iterMean (expTwist C' W) j c := e
  simp only [FullSpace.AsDifferentials.iterLogRatio, iterRatio, e']
section Maps
variable (h₄ : Tower.BlockPathContourPivotStatement)
  (hRel : FullSpace.CovariantIterRelations)
  (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
  (hD : YangMills.Construction.Tower.FullSpace.AsDifferentials.Requirements L k)
  (hR : YangMills.Construction.Tower.SupportOfMeans.Unbounded.SideRequirements L k)
  {U : Edge L k 0 → Matrices.ComplexMatrix2} (hU : U ∈ smallIterateFields L k)
include hRel hL hU in
theorem complexIterDeriv_zero_level {B : Edge L k 0 → Matrices.ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) : complexIterDeriv L k 0 U B = B := by
  have e := (hRel L hL k 0 (Nat.zero_le _) U hU).1 B hB
  simp only [iterCovariantDeriv, iterContourLogDrift, covDiff_zero, add_zero] at e
  exact e.symm
include hD hR hU in
theorem complexIterDeriv_succ_congr {i : ℕ} (hi : i < k) {c : Edge L k (i + 1)}
    (hc : c.IsPositivelyOriented) {B B' : Edge L k 0 → Matrices.ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) (hB' : B' ∈ complexEdgeForms (meshAt L k 0))
    (h : ∀ v ∈ supportEdges c, B v = B' v) :
    complexIterDeriv L k (i + 1) U B c = complexIterDeriv L k (i + 1) U B' c := by
  have hS := hD.1 i hi _ (hU.2 i hi) U hU
  have d : HasDerivAt _ _ _ := hS.deriv_iter c hc B hB
  have d' : HasDerivAt _ _ _ := hS.deriv_iter c hc B' hB'
  obtain ⟨hfin, -⟩ := hR.finite_nonempty (i + 1) (by omega) c
  have hRead := hR.dependsOnlyOn (i + 1) (by omega) c hfin.toFinset (by simp)
  have e : (fun t : ℂ => FullSpace.AsDifferentials.iterLogRatio U (i + 1) c (t • B)) =
      fun t : ℂ => FullSpace.AsDifferentials.iterLogRatio U (i + 1) c (t • B') := by
    funext t
    refine iterLogRatio_congr hRead hU.1 (Submodule.smul_mem _ _ hB)
      (Submodule.smul_mem _ _ hB') fun v hv => ?_
    simp [h v (hfin.mem_toFinset.1 hv)]
  rw [e] at d
  exact d.unique d'
include hRel hL hD hR hU in
theorem complexIterDeriv_congr {j : ℕ} (hj : j ≤ k) {c : Edge L k j}
    (hc : c.IsPositivelyOriented) {B B' : Edge L k 0 → Matrices.ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) (hB' : B' ∈ complexEdgeForms (meshAt L k 0))
    (h : ∀ v ∈ supportEdges c, B v = B' v) :
    complexIterDeriv L k j U B c = complexIterDeriv L k j U B' c := by
  cases j with
  | zero =>
    rw [complexIterDeriv_zero_level hRel hL hU hB, complexIterDeriv_zero_level hRel hL hU hB']
    exact h c ⟨hc, Or.inl (mem_verticesOfOrder_zero c.initial),
      Or.inr (mem_verticesOfOrder_zero c.terminal)⟩
  | succ i => exact complexIterDeriv_succ_congr hD hR hU (by omega) hc hB hB' h
include h₄ hL hk in
theorem iterAdjointCubeAverage_congr (U : Edge L k 0 → Matrices.ComplexMatrix2) :
    ∀ j ≤ k, ∀ (y : Vertex L k j) (l l' : Vertex L k 0 → Matrices.ComplexMatrix2),
      (∀ x ∈ verticesOfOrder j y, l x = l' x) →
      iterAdjointCubeAverage L k U j l y = iterAdjointCubeAverage L k U j l' y := by
  intro j
  induction j with
  | zero =>
    intro _ y l l' h
    exact h y (mem_verticesOfOrder_zero y)
  | succ j ih =>
    intro hj y l l' h
    simp only [iterAdjointCubeAverage, adjointCubeAverage]
    refine congrArg _ (finsum_mem_congr rfl fun x hx => ?_)
    rw [ih (by omega) x l l' fun z hz => h z (verticesOfOrder_subset_succ h₄ hL hk (by omega) hx hz)]
include h₄ hRel hL hk hD hR hU in
theorem iterContourLogDrift_congr : ∀ j ≤ k, ∀ (y : Vertex L k j)
    (B B' : Edge L k 0 → Matrices.ComplexMatrix2), B ∈ complexEdgeForms (meshAt L k 0) →
    B' ∈ complexEdgeForms (meshAt L k 0) → (∀ v ∈ edgesOfOrder j y, B v = B' v) →
      iterContourLogDrift L k U j B y = iterContourLogDrift L k U j B' y := by
  intro j
  induction j with
  | zero =>
    intro _ y B B' _ _ _
    rfl
  | succ j ih =>
    intro hj y B B' hB hB' h
    have hj' : j < k := by omega
    simp only [iterContourLogDrift, Pi.add_apply]
    refine congrArg₂ (· + ·) ?_ ?_
    · simp only [adjointCubeAverage]
      refine congrArg _ (finsum_mem_congr rfl fun x hx => ?_)
      have inc := verticesOfOrder_subset_succ h₄ hL hk hj' (y := y) (x := x) hx
      rw [ih (by omega) x B B' hB hB' fun v hv => h v ⟨hv.1, inc hv.2.1, inc hv.2.2⟩]
    · refine contourLogDrift_congr h₄ hL hk hj' _ _ _ y fun c hc ht hh => ?_
      refine complexIterDeriv_congr hRel hL hD hR hU (by omega) hc hB hB' fun v hv => h v ?_
      have inc₁ := verticesOfOrder_subset_succ h₄ hL hk hj' (y := y) (x := c.initial) ht
      have inc₂ := verticesOfOrder_subset_succ h₄ hL hk hj' (y := y) (x := c.terminal) hh
      refine ⟨hv.1, ?_, ?_⟩
      · rcases hv.2.1 with h' | h'
        · exact inc₁ h'
        · exact inc₂ h'
      · rcases hv.2.2 with h' | h'
        · exact inc₁ h'
        · exact inc₂ h'
include h₄ hRel hL hk hD hR hU in
theorem iterCovariantDeriv_congr {c : Edge L k k} (hc : c.IsPositivelyOriented)
    {B B' : Edge L k 0 → Matrices.ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k 0))
    (hB' : B' ∈ complexEdgeForms (meshAt L k 0)) (h : ∀ v ∈ supportEdges c, B v = B' v) :
    iterCovariantDeriv L k U k B c = iterCovariantDeriv L k U k B' c := by
  have rel := (hRel L hL k k le_rfl U hU).1
  rw [rel B hB, rel B' hB']
  simp only [Pi.add_apply, covDiff_of_isPositivelyOriented _ _ hc]
  rw [complexIterDeriv_congr hRel hL hD hR hU le_rfl hc hB hB' h,
    iterContourLogDrift_congr h₄ hRel hL hk hD hR hU k le_rfl c.terminal B B' hB hB'
      fun v hv => h v ⟨hv.1, Or.inr hv.2.1, Or.inr hv.2.2⟩,
    iterContourLogDrift_congr h₄ hRel hL hk hD hR hU k le_rfl c.initial B B' hB hB'
      fun v hv => h v ⟨hv.1, Or.inl hv.2.1, Or.inl hv.2.2⟩]
include hRel hL hD hU in
theorem complexIterDeriv_zero {j : ℕ} (hj : j ≤ k) :
    complexIterDeriv L k j U 0 = 0 := by
  cases j with
  | zero => exact complexIterDeriv_zero_level hRel hL hU (Submodule.zero_mem _)
  | succ i =>
    have hS := hD.1 i (by omega) _ (hU.2 i (by omega)) U hU
    have e := (hS.linear_iter 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 0).2
    simpa using e
include hRel hL hD hU in
theorem iterContourLogDrift_zero : ∀ j ≤ k, iterContourLogDrift L k U j 0 = 0 := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hS := hD.1 j (by omega) _ (hU.2 j (by omega)) U hU
    have e := (hS.linear_contour 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 0).2
    have e₀ : contourLogDrift (complexIter L k j U) (0 : Edge L k j → Matrices.ComplexMatrix2) = 0 := by
      simpa using e
    have e₁ : adjointCubeAverage (complexIter L k j U)
        (0 : Vertex L k j → Matrices.ComplexMatrix2) = 0 := by
      funext y
      simp [adjointCubeAverage, Matrices.ComplexMatrix2.conjugateBy]
    simp only [iterContourLogDrift]
    rw [ih (by omega), complexIterDeriv_zero hRel hL hD hU (by omega), e₀, e₁, add_zero]
include hRel hL hD hU in
theorem iterCovariantDeriv_zero : iterCovariantDeriv L k U k 0 = 0 := by
  rw [(hRel L hL k k le_rfl U hU).1 0 (Submodule.zero_mem _),
    complexIterDeriv_zero hRel hL hD hU le_rfl,
    iterContourLogDrift_zero hRel hL hD hU k le_rfl, covDiff_zero, add_zero]
end Maps
theorem IsFinitelySupportedForm.mem_boundedSubmodule {B : Edge L k 0 → Matrices.ComplexMatrix2}
    (hB : IsFinitelySupportedForm B) :
    B ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0)) := by
  have hf : (Function.support (restrictToPositiveEdges B)).Finite := hB.2
  have hp : ∀ p : PositiveEdge (meshAt L k 0),
      ‖B p.1‖ ≤ ∑ q ∈ hf.toFinset, ‖B q.1‖ := by
    intro p
    by_cases hs : p ∈ Function.support (restrictToPositiveEdges B)
    · exact Finset.single_le_sum (f := fun q : PositiveEdge (meshAt L k 0) => ‖B q.1‖)
        (fun _ _ => norm_nonneg _) (hf.mem_toFinset.2 hs)
    · have h0 : B p.1 = 0 := by simpa [restrictToPositiveEdges] using hs
      rw [h0, norm_zero]
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨hB.1, ∑ q ∈ hf.toFinset, ‖B q.1‖, fun v => ?_⟩
  by_cases hv : v.IsPositivelyOriented
  · exact hp ⟨v, hv⟩
  · have hr : IsEdgeFormIn PeriodicLattice.complexLieAlgebra B := hB.1
    have e : ‖B v‖ = ‖B v.opposite‖ := by rw [hr.2 v, norm_neg]
    change ‖B v‖ ≤ _
    rw [e]
    exact hp ⟨v.opposite, opposite_isPositivelyOriented_of_not hv⟩
theorem isFinitelySupportedForm_zero :
    IsFinitelySupportedForm (0 : Edge L k 0 → Matrices.ComplexMatrix2) :=
  ⟨Submodule.zero_mem _, by
    have e : Function.support
        (restrictToPositiveEdges (0 : Edge L k 0 → Matrices.ComplexMatrix2)) = ∅ := by
      ext p
      simp [restrictToPositiveEdges]
    change (Function.support _).Finite
    rw [e]
    exact finite_empty⟩
theorem complexQuadraticTerm_congr
    (hR : YangMills.Construction.Tower.SupportOfMeans.Unbounded.SideRequirements L k)
    {U : Edge L k 0 → Matrices.ComplexMatrix2} (hW : U ∈ baseFields L k)
    (hq : HasUniqueQuadraticTerm (complexEdgeForms (meshAt L k 0)) (topLogRatio L k U)
      (topDeriv L k U))
    (c : PositiveEdge (meshAt L k k)) {B₁ B₁' B₂ B₂' : Edge L k 0 → Matrices.ComplexMatrix2}
    (h₁ : IsFinitelySupportedForm B₁) (h₁' : IsFinitelySupportedForm B₁')
    (h₂ : IsFinitelySupportedForm B₂) (h₂' : IsFinitelySupportedForm B₂')
    (h : ∀ v ∈ supportEdges c.1, B₁ v = B₁' v ∧ B₂ v = B₂' v) :
    complexQuadraticTerm L k U B₁ B₂ c = complexQuadraticTerm L k U B₁' B₂' c := by
  obtain ⟨hfin, -⟩ := hR.finite_nonempty k le_rfl c.1
  have hRead := hR.dependsOnlyOn k le_rfl c.1 hfin.toFinset (by simp)
  have e : ∀ s t : ℂ, topLogRatio L k U c (algebraMap ℂ ℂ s • B₁ + algebraMap ℂ ℂ t • B₂) =
      topLogRatio L k U c (algebraMap ℂ ℂ s • B₁' + algebraMap ℂ ℂ t • B₂') := by
    intro s t
    refine iterLogRatio_congr hRead hW ?_ ?_ fun v hv => ?_
    · exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁.1) (Submodule.smul_mem _ _ h₂.1)
    · exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁'.1) (Submodule.smul_mem _ _ h₂'.1)
    · obtain ⟨e₁, e₂⟩ := h v (hfin.mem_toFinset.1 hv)
      simp [e₁, e₂]
  have m := (hq.2.2 ⟨B₁, h₁.mem_boundedSubmodule⟩ ⟨B₂, h₂.mem_boundedSubmodule⟩ c).1
  have m' := (hq.2.2 ⟨B₁', h₁'.mem_boundedSubmodule⟩ ⟨B₂', h₂'.mem_boundedSubmodule⟩ c).1
  simp only [complexQuadraticTerm, quadraticTermAt,
    dif_pos (And.intro h₁.mem_boundedSubmodule h₂.mem_boundedSubmodule),
    dif_pos (And.intro h₁'.mem_boundedSubmodule h₂'.mem_boundedSubmodule)]
  rw [← m, ← m']
  simp only [mixedDirectionalDeriv, e]
theorem complexQuadraticTerm_zero_left {U B : Edge L k 0 → Matrices.ComplexMatrix2}
    (hB : IsFinitelySupportedForm B) :
    complexQuadraticTerm L k U 0 B = 0 := by
  have h0 := isFinitelySupportedForm_zero (L := L) (k := k)
  simp only [complexQuadraticTerm, quadraticTermAt,
    dif_pos (And.intro h0.mem_boundedSubmodule hB.mem_boundedSubmodule)]
  have e : (⟨0, h0.mem_boundedSubmodule⟩ : boundedSubmodule (complexEdgeForms (meshAt L k 0))) = 0 :=
    rfl
  rw [e, map_zero, LinearMap.zero_apply]
def nonzeroEdges (B : Edge L k 0 → Matrices.ComplexMatrix2) : Set (Edge L k 0) :=
  Subtype.val '' Function.support (restrictToPositiveEdges B)
theorem eq_zero_of_notMem_nonzeroEdges {B : Edge L k 0 → Matrices.ComplexMatrix2} {v : Edge L k 0}
    (hp : v.IsPositivelyOriented) (hv : v ∉ nonzeroEdges B) : B v = 0 := by
  by_contra hne
  exact hv ⟨⟨v, hp⟩, hne, rfl⟩
section Counting
variable (h₄ : Tower.BlockPathContourPivotStatement)
  (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
include h₄ hL hk in
theorem encard_edges_le (v : Edge L k 0) :
    {c : Edge L k k | c.IsPositivelyOriented ∧ v ∈ supportEdges c}.encard ≤ 8 := by
  have H := (h₄ L hL k k k hk le_rfl le_rfl).2.2.2.2.2.1.encard_le_eight
  rw [Nat.sub_self] at H
  refine (encard_le_encard ?_).trans (H v)
  rintro c ⟨hc, hv⟩
  exact ⟨hc, hv.2.1, hv.2.2⟩
include h₄ hL hk in
theorem encard_vertices_le (v : Edge L k 0) :
    {y : Vertex L k k | v ∈ cubePositiveEdges y}.encard ≤ 1 := by
  have H := (h₄ L hL k k k hk le_rfl le_rfl).2.1.existsUnique_mem
  rw [Nat.sub_self] at H
  refine encard_le_one_iff.2 fun y y' hy hy' => ?_
  exact (H v.initial).unique hy.2.1 hy'.2.1
include h₄ hL hk in
theorem finite_edges (v : Edge L k 0) :
    {c : PositiveEdge (meshAt L k k) | v ∈ supportEdges c.1}.Finite := by
  have hf : {c : Edge L k k | c.IsPositivelyOriented ∧ v ∈ supportEdges c}.Finite :=
    finite_of_encard_le_coe (k := 8) (encard_edges_le h₄ hL hk v)
  refine (hf.preimage Subtype.val_injective.injOn).subset fun c hc => ?_
  exact ⟨c.2, hc⟩
include h₄ hL hk in
theorem finite_vertices (v : Edge L k 0) :
    {y : Vertex L k k | v ∈ cubePositiveEdges y}.Finite :=
  finite_of_encard_le_coe (k := 1) (encard_vertices_le h₄ hL hk v)
end Counting
theorem IsFinitelySupportedForm.finite_nonzeroEdges {B : Edge L k 0 → Matrices.ComplexMatrix2}
    (hB : IsFinitelySupportedForm B) : (nonzeroEdges B).Finite :=
  Set.Finite.image _ hB.2
section Supports
variable (h₄ : Tower.BlockPathContourPivotStatement)
  (hRel : FullSpace.CovariantIterRelations)
  (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
  (hD : YangMills.Construction.Tower.FullSpace.AsDifferentials.Requirements L k)
  (hR : YangMills.Construction.Tower.SupportOfMeans.Unbounded.SideRequirements L k)
  {U : Edge L k 0 → Matrices.ComplexMatrix2} (hU : U ∈ smallIterateFields L k)
include h₄ hRel hL hk hD hR hU in
theorem iterCovariantDeriv_hasFiniteSupp {B : Edge L k 0 → Matrices.ComplexMatrix2}
    (hB : IsFinitelySupportedForm B) :
    HasFiniteSupp (restrictToPositiveEdges (iterCovariantDeriv L k U k B)) := by
  refine hasFiniteSupp_of_vanishing hB.finite_nonzeroEdges
    (fun c : PositiveEdge (meshAt L k k) => supportEdges c.1)
    (fun v _ => finite_edges h₄ hL hk v) fun c hc => ?_
  have e := iterCovariantDeriv_congr h₄ hRel hL hk hD hR hU c.2 hB.1
    (Submodule.zero_mem (complexEdgeForms (meshAt L k 0))) fun v hv =>
      eq_zero_of_notMem_nonzeroEdges hv.1 (hc v hv)
  have z := iterCovariantDeriv_zero hRel hL hD hU
  change iterCovariantDeriv L k U k B c.1 = 0
  rw [e, z]
  rfl
include h₄ hL hk hR in
theorem complexQuadraticTerm_hasFiniteSupp (hW : U ∈ baseFields L k)
    (hq : HasUniqueQuadraticTerm (complexEdgeForms (meshAt L k 0)) (topLogRatio L k U)
      (topDeriv L k U))
    {B B' : Edge L k 0 → Matrices.ComplexMatrix2} (hB : IsFinitelySupportedForm B)
    (hB' : IsFinitelySupportedForm B') : HasFiniteSupp (complexQuadraticTerm L k U B B') := by
  refine hasFiniteSupp_of_vanishing hB.finite_nonzeroEdges
    (fun c : PositiveEdge (meshAt L k k) => supportEdges c.1)
    (fun v _ => finite_edges h₄ hL hk v) fun c hc => ?_
  have e := complexQuadraticTerm_congr hR hW hq c hB isFinitelySupportedForm_zero hB' hB'
    fun v hv => ⟨eq_zero_of_notMem_nonzeroEdges hv.1 (hc v hv), rfl⟩
  rw [e, complexQuadraticTerm_zero_left hB']
  rfl
include h₄ hRel hL hk hD hR hU in
theorem iterContourLogDrift_hasFiniteSupp {B : Edge L k 0 → Matrices.ComplexMatrix2}
    (hB : IsFinitelySupportedForm B) :
    HasFiniteSupp (iterContourLogDrift L k U k B) := by
  refine hasFiniteSupp_of_vanishing hB.finite_nonzeroEdges
    (fun y : Vertex L k k => cubePositiveEdges y)
    (fun v _ => finite_vertices h₄ hL hk v) fun y hy => ?_
  have e := iterContourLogDrift_congr h₄ hRel hL hk hD hR hU k le_rfl y B 0 hB.1
    (Submodule.zero_mem _) fun v hv => eq_zero_of_notMem_nonzeroEdges hv.1 (hy v hv)
  rw [e, iterContourLogDrift_zero hRel hL hD hU k le_rfl]
  rfl
include h₄ hRel hL hk hD hR hU in
theorem localAt_of_small : LocalAt U := by
  have hq := hD.2 U hU
  refine ⟨fun c B B' hB hB' h => ?_, fun c B₁ B₁' B₂ B₂' a₁ a₁' a₂ a₂' h => ?_,
    fun y B B' hB hB' h => ?_, fun y l l' h => ?_, fun B hB => ?_, fun B B' hB hB' => ?_,
    fun B hB => ?_⟩
  · exact iterCovariantDeriv_congr h₄ hRel hL hk hD hR hU c.2 hB.1 hB'.1 h
  · exact complexQuadraticTerm_congr hR hU.1 hq c a₁ a₁' a₂ a₂' h
  · exact iterContourLogDrift_congr h₄ hRel hL hk hD hR hU k le_rfl y B B' hB.1 hB'.1 h
  · exact iterAdjointCubeAverage_congr h₄ hL hk U k le_rfl y l l' h
  · exact iterCovariantDeriv_hasFiniteSupp h₄ hRel hL hk hD hR hU hB
  · exact complexQuadraticTerm_hasFiniteSupp h₄ hL hk hR hU.1 hq hB hB'
  · exact iterContourLogDrift_hasFiniteSupp h₄ hRel hL hk hD hR hU hB
end Supports
theorem statement_holds (h₁ : Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (h₂ : Tower.SupportOfMeans.SupportOfMeansHolds)
    (h₃ : FullSpace.CovariantIterRelations)
    (h₄ : Tower.BlockPathContourPivotStatement) : Statement := by
  intro L hL k hk
  exact ⟨fun U hU => localAt_of_small h₄ h₃ hL hk (h₁ L hL k hk).2 (h₂ L hL k hk).2 hU,
    encard_edges_le h₄ hL hk, encard_vertices_le h₄ hL hk⟩
end YangMills.Construction.Tower.FullSpace.ReadsCubes
end
