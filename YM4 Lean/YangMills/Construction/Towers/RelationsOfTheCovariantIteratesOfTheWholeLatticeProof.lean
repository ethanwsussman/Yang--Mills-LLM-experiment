import YangMills.Construction.Towers.BlockAverageTimesItsTransposeAtTheSideInfinity
import YangMills.Construction.Towers.ChainOfTheComplexIteratesAtTheSideInfinity
import YangMills.Construction.Towers.LinearityOfTheCovariantStepAtTheSideInfinity
import YangMills.Construction.Towers.RelationAndBoundsOfTheIteratesOnTheWholeLatticeProof
import YangMills.Construction.Towers.RelationsOfOneCovariantStepAtTheSideInfinity
import YangMills.Construction.Towers.RelationsOfTheCovariantIteratesOfTheWholeLattice
import YangMills.Construction.Towers.RelationsOfTheCovariantIteratesOnTheSidesProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.CovariantIterRelationsProof
theorem extendOddly_add {a : ℝ} (f g : InfiniteLattice.Link a → ComplexMatrix2) :
    extendOddly (f + g) = extendOddly f + extendOddly g := by
  funext e
  by_cases he : e.IsPositivelyOriented
  · simp [extendOddly, he]
  · simp [extendOddly, he, add_comm]
theorem covDiff_zero {a : ℝ} (W : InfiniteLattice.Link a → ComplexMatrix2) :
    covDiff W (0 : InfiniteLattice.LatticePoint a → ComplexMatrix2) = 0 := by
  funext e
  by_cases he : e.IsPositivelyOriented
  · simp [covDiff, extendOddly, he, ComplexMatrix2.conjugateBy]
  · simp [covDiff, extendOddly, he, ComplexMatrix2.conjugateBy]
theorem covDiff_add {a : ℝ} (W : InfiniteLattice.Link a → ComplexMatrix2)
    (u v : InfiniteLattice.LatticePoint a → ComplexMatrix2) :
    covDiff W (u + v) = covDiff W u + covDiff W v := by
  unfold covDiff
  rw [← extendOddly_add]
  congr 1
  funext e
  simp only [Pi.add_apply, ComplexMatrix2.conjugateBy, mul_add, add_mul]
  abel
theorem latticeSubgroup_meshAt_succ_subset (L k j : ℕ) (hL : L ≠ 0) :
    (InfiniteLattice.latticeSubgroup (meshAt L k (j + 1)) : Set AmbientSpace) ⊆
      InfiniteLattice.latticeSubgroup (meshAt L k j) := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.latticeSubgroup_meshAt_succ_subset <;> assumption
theorem latticeSubgroup_meshAt_subset_zero (L k j : ℕ) (hL : L ≠ 0) :
    (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) ⊆
      InfiniteLattice.latticeSubgroup (meshAt L k 0) := by
  induction j with
  | zero => exact subset_rfl
  | succ j ih => exact (latticeSubgroup_meshAt_succ_subset L k j hL).trans ih
theorem restrictVertexFunction_self {a : ℝ} (u : InfiniteLattice.LatticePoint a → ComplexMatrix2) :
    restrictVertexFunction a u = u := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.restrict_self <;> assumption
theorem restrictVertexFunction_restrictVertexFunction {a a' a'' : ℝ}
    (h₁ : (InfiniteLattice.latticeSubgroup a'' : Set AmbientSpace) ⊆
      InfiniteLattice.latticeSubgroup a')
    (h₂ : (InfiniteLattice.latticeSubgroup a' : Set AmbientSpace) ⊆
      InfiniteLattice.latticeSubgroup a)
    (u : InfiniteLattice.LatticePoint a → ComplexMatrix2) :
    restrictVertexFunction a'' (restrictVertexFunction a' u) = restrictVertexFunction a'' u := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.restrict_restrict <;> assumption
section IterateRelations
variable (hC : ComplexIterChain) (hR : CovariantStepRelations)
  (hN : CovariantStepComplexLinear)
  {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) {U : Edge L k 0 → ComplexMatrix2}
  (hU : U ∈ smallIterateFields L k)
include hN hL hU
theorem adjointCubeAverage_add {j : ℕ} (hj : j < k) {u v : Vertex L k j → ComplexMatrix2}
    (hu : ∀ x, u x ∈ ComplexMatrix2.traceless) (hv : ∀ x, v x ∈ ComplexMatrix2.traceless) :
    adjointCubeAverage (complexIter L k j U) (u + v) =
      adjointCubeAverage (complexIter L k j U) u +
        adjointCubeAverage (complexIter L k j U) v := by
  have H := ((hN L hL k j hj _ (hU.2 j hj)).2.2.2 u v hu hv 1).2
  simpa only [one_smul] using H
theorem covariantSmoothingDeriv_add {j : ℕ} (hj : j < k) {A A' : Edge L k j → ComplexMatrix2}
    (hA : A ∈ complexEdgeForms (meshAt L k j)) (hA' : A' ∈ complexEdgeForms (meshAt L k j)) :
    covariantSmoothingDeriv (complexIter L k j U) (A + A') =
      covariantSmoothingDeriv (complexIter L k j U) A +
        covariantSmoothingDeriv (complexIter L k j U) A' := by
  have H := (hN L hL k j hj _ (hU.2 j hj)).2.1 A hA A' hA' 1
  simp only [one_smul] at H
  unfold covariantSmoothingDeriv
  rw [H.1, H.2, covDiff_add]
  abel
theorem iterAdjointCubeAverage_mem_traceless {u : Vertex L k 0 → ComplexMatrix2}
    (hu : ∀ x, u x ∈ ComplexMatrix2.traceless) (j : ℕ)
    (hj : j ≤ k) : ∀ y, iterAdjointCubeAverage L k U j u y ∈ ComplexMatrix2.traceless := by
  induction j with
  | zero => exact hu
  | succ j ih =>
    have hjk : j < k := hj
    exact ((hN L hL k j hjk _ (hU.2 j hjk)).2.2.1 _ (ih hjk.le)).2
include hC
theorem iterContourLogDrift_mem_traceless {A : Edge L k 0 → ComplexMatrix2}
    (hA : A ∈ complexEdgeForms (meshAt L k 0))
    (j : ℕ) (hj : j ≤ k) : ∀ y, iterContourLogDrift L k U j A y ∈ ComplexMatrix2.traceless := by
  induction j with
  | zero => exact fun _ => ComplexMatrix2.traceless.zero_mem
  | succ j ih =>
    have hjk : j < k := hj
    have hlin := hN L hL k j hjk _ (hU.2 j hjk)
    intro y
    exact ComplexMatrix2.traceless.add_mem ((hlin.2.2.1 _ (ih hjk.le)).2 y)
      ((hlin.1 _ ((hC L hL k U hU A hA).2.2 j hjk.le)).2 y)
include hR
theorem iterCovariantDeriv_eq {A : Edge L k 0 → ComplexMatrix2}
    (hA : A ∈ complexEdgeForms (meshAt L k 0))
    (j : ℕ) (hj : j ≤ k) :
    iterCovariantDeriv L k U j A =
      complexIterDeriv L k j U A +
        covDiff (complexIter L k j U) (iterContourLogDrift L k U j A) := by
  induction j with
  | zero =>
    change A = complexIterDeriv L k 0 U A + covDiff U 0
    rw [(hC L hL k U hU A hA).1, covDiff_zero, add_zero]
  | succ j ih =>
    have hjk : j < k := hj
    have hW := hU.2 j hjk
    have hlin := hN L hL k j hjk _ hW
    have hQ := (hC L hL k U hU A hA).2.2 j hjk.le
    have hmem := iterContourLogDrift_mem_traceless hC hN hL hU hA j hjk.le
    change covariantSmoothingDeriv (complexIter L k j U)
        (iterCovariantDeriv L k U j A) =
      complexIterDeriv L k (j + 1) U A +
        covDiff (smoothingMap L k j (complexIter L k j U))
          (adjointCubeAverage (complexIter L k j U) (iterContourLogDrift L k U j A) +
            contourLogDrift (complexIter L k j U) (complexIterDeriv L k j U A))
    rw [ih hjk.le, covariantSmoothingDeriv_add hN hL hU hjk hQ (hlin.2.2.1 _ hmem).1,
      (hR L hL k j hjk _ hW _ hmem).2.2, (hC L hL k U hU A hA).2.1 j hjk, covDiff_add]
    unfold covariantSmoothingDeriv
    abel
theorem complexIterDeriv_covDiff {u : Vertex L k 0 → ComplexMatrix2}
    (hu : ∀ x, u x ∈ ComplexMatrix2.traceless)
    (hk : 0 < k) (j : ℕ) (hj : j ≤ k) :
    complexIterDeriv L k j U (covDiff U u) =
      covDiff (complexIter L k j U) (restrictVertexFunction (meshAt L k j) u) := by
  have hL0 : L ≠ 0 := by have := hL.2; omega
  have hD : covDiff U u ∈ complexEdgeForms (meshAt L k 0) :=
    ((hN L hL k 0 hk U (hU.2 0 hk)).2.2.1 u hu).1
  induction j with
  | zero =>
    rw [(hC L hL k U hU _ hD).1, restrictVertexFunction_self]
    rfl
  | succ j ih =>
    have hjk : j < k := hj
    have hr : ∀ x, restrictVertexFunction (meshAt L k j) u x ∈ ComplexMatrix2.traceless :=
      fun x => hu _
    rw [(hC L hL k U hU _ hD).2.1 j hjk, ih hjk.le, ((hR L hL k j hjk _ (hU.2 j hjk)) _ hr).1,
      restrictVertexFunction_restrictVertexFunction (latticeSubgroup_meshAt_succ_subset L k j hL0)
        (latticeSubgroup_meshAt_subset_zero L k j hL0)]
    rfl
theorem iterAdjointCubeAverage_eq {u : Vertex L k 0 → ComplexMatrix2}
    (hu : ∀ x, u x ∈ ComplexMatrix2.traceless) (j : ℕ)
    (hj : j ≤ k) :
    iterAdjointCubeAverage L k U j u =
      restrictVertexFunction (meshAt L k j) u +
        iterContourLogDrift L k U j (covDiff U u) := by
  have hL0 : L ≠ 0 := by have := hL.2; omega
  induction j with
  | zero =>
    change u = restrictVertexFunction (meshAt L k 0) u + 0
    rw [restrictVertexFunction_self, add_zero]
  | succ j ih =>
    have hjk : j < k := hj
    have hk : 0 < k := by omega
    have hD : covDiff U u ∈ complexEdgeForms (meshAt L k 0) :=
      ((hN L hL k 0 hk U (hU.2 0 hk)).2.2.1 u hu).1
    have hr : ∀ x, restrictVertexFunction (meshAt L k j) u x ∈ ComplexMatrix2.traceless :=
      fun x => hu _
    change adjointCubeAverage (complexIter L k j U) (iterAdjointCubeAverage L k U j u) =
      restrictVertexFunction (meshAt L k (j + 1)) u +
        (adjointCubeAverage (complexIter L k j U)
            (iterContourLogDrift L k U j (covDiff U u)) +
          contourLogDrift (complexIter L k j U)
            (complexIterDeriv L k j U (covDiff U u)))
    rw [ih hjk.le,
      adjointCubeAverage_add hN hL hU hjk hr (iterContourLogDrift_mem_traceless hC hN hL hU hD j hjk.le),
      complexIterDeriv_covDiff hC hR hN hL hU hu hk j hjk.le,
      ((hR L hL k j hjk _ (hU.2 j hjk)) _ hr).2.1,
      restrictVertexFunction_restrictVertexFunction (latticeSubgroup_meshAt_succ_subset L k j hL0)
        (latticeSubgroup_meshAt_subset_zero L k j hL0)]
    abel
omit hC in
theorem iterCovariantDeriv_covDiff {u : Vertex L k 0 → ComplexMatrix2}
    (hu : ∀ x, u x ∈ ComplexMatrix2.traceless) (j : ℕ)
    (hj : j ≤ k) :
    iterCovariantDeriv L k U j (covDiff U u) =
      covDiff (complexIter L k j U) (iterAdjointCubeAverage L k U j u) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hjk : j < k := hj
    change covariantSmoothingDeriv (complexIter L k j U)
        (iterCovariantDeriv L k U j (covDiff U u)) = _
    rw [ih hjk.le]
    exact ((hR L hL k j hjk _ (hU.2 j hjk)) _
      (iterAdjointCubeAverage_mem_traceless hN hL hU hu j hjk.le)).2.2
end IterateRelations
section UnivTransposes
variable {α β : Type}
abbrev TracelessFn (α : Type) : Type := ↥(pairedFunctions α).complexSubmodule
theorem mem_complexSubmodule_iff {f : α → ComplexMatrix2} :
    f ∈ (pairedFunctions α).complexSubmodule ↔ ∀ i, f i ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.IterRelationsProof.mem_complexSubmodule_iff <;> assumption
def toUniv (α : Type) : TracelessFn α →ₗ[ℂ] TracelessFn (univ : Set α) where
  toFun f := ⟨fun x => f.1 x.1,
    mem_complexSubmodule_iff.2 fun x => mem_complexSubmodule_iff.1 f.2 x.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def ofUniv (α : Type) : TracelessFn (univ : Set α) →ₗ[ℂ] TracelessFn α where
  toFun f := ⟨fun x => f.1 ⟨x, mem_univ x⟩,
    mem_complexSubmodule_iff.2 fun _ => mem_complexSubmodule_iff.1 f.2 _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem finitelySupported_toUniv {f : TracelessFn α}
    (h : (pairedFunctions α).IsFinitelySupported f.1) :
    (pairedFunctions (univ : Set α)).IsFinitelySupported (toUniv α f).1 :=
  Set.Finite.preimage (f := Subtype.val (p := (· ∈ (univ : Set α))))
    Subtype.val_injective.injOn (show (Function.support f.1).Finite from h)
theorem finitelySupported_ofUniv {f : TracelessFn (univ : Set α)}
    (h : (pairedFunctions (univ : Set α)).IsFinitelySupported f.1) :
    (pairedFunctions α).IsFinitelySupported (ofUniv α f).1 :=
  Set.Finite.preimage (f := fun x : α => (⟨x, mem_univ x⟩ : (univ : Set α)))
    (fun _ _ _ _ hxy => congrArg Subtype.val hxy) (show (Function.support f.1).Finite from h)
theorem pair_toUniv (f g : TracelessFn α) :
    (pairedFunctions (univ : Set α)).pair (toUniv α f).1 (toUniv α g).1 =
      (pairedFunctions α).pair f.1 g.1 :=
  finsum_comp_equiv (Equiv.Set.univ α).symm.symm
    (f := fun i => ComplexMatrix2.halfTrace (f.1 i * g.1 i))
theorem hasUniqueTranspose_of_univ
    (H : LeftChartFields.HasUniqueTranspose (pairedFunctions (univ : Set α))
      (pairedFunctions (univ : Set β))) :
    LeftChartFields.HasUniqueTranspose (pairedFunctions α) (pairedFunctions β) := by
  intro T hT
  obtain ⟨T', h₁, h₂⟩ := H (toUniv β ∘ₗ T ∘ₗ ofUniv α)
    fun f hf => finitelySupported_toUniv (hT _ (finitelySupported_ofUniv hf))
  refine ⟨ofUniv α ∘ₗ T' ∘ₗ toUniv β, fun g f hf => ?_, fun R hR => ?_⟩
  · have H1 := h₁ (toUniv β g) (toUniv α f) (finitelySupported_toUniv hf)
    exact (pair_toUniv (ofUniv α (T' (toUniv β g))) f).symm.trans
      (H1.trans (pair_toUniv g (T f)))
  · have hR' := h₂ (fun g => toUniv α (R (ofUniv β g))) fun g f hf => by
      have H1 := hR (ofUniv β g) (ofUniv α f) (finitelySupported_ofUniv hf)
      exact (pair_toUniv (R (ofUniv β g)) (ofUniv α f)).trans
        (H1.trans (pair_toUniv (ofUniv β g) (T (ofUniv α f))).symm)
    funext g
    exact congrArg (ofUniv α) (congrFun hR' (toUniv β g))
theorem transposeMap_spec {S S' : PairedFunctionSpace}
    (H : LeftChartFields.HasUniqueTranspose S S')
    (T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule)
    (hT : PairedFunctionSpace.PreservesFiniteSupport T) :
    PairedFunctionSpace.IsTransposeMap T (PairedFunctionSpace.transposeMap T) ∧
      ∀ R : S'.complexSubmodule → S.complexSubmodule,
        (∀ (g : S'.complexSubmodule) (f : S.complexSubmodule), S.IsFinitelySupported f →
          S.pair (R g) f = S'.pair g (T f)) → R = PairedFunctionSpace.transposeMap T := by
  obtain ⟨T', h₁, h₂⟩ := H T hT
  have hs : PairedFunctionSpace.IsTransposeMap T (PairedFunctionSpace.transposeMap T) :=
    Classical.epsilon_spec ⟨T', h₁⟩
  have hT' : PairedFunctionSpace.transposeMap T = T' := DFunLike.coe_injective (h₂ _ hs)
  rw [hT']
  exact ⟨h₁, h₂⟩
end UnivTransposes
theorem iterAdjointCubeAverage_mul_transpose (hP : LeftChartFields.Claim)
    (hA : CubeAverageMulTranspose.Statement) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k) (j : ℕ) (hj : j ≤ k) :
    ∃ T : (pairedFunctions (Vertex L k 0)).complexSubmodule →ₗ[ℂ]
        (pairedFunctions (Vertex L k j)).complexSubmodule,
      (∀ u : (pairedFunctions (Vertex L k 0)).complexSubmodule,
        (T u : (pairedFunctions (Vertex L k j)).index → ComplexMatrix2) =
          iterAdjointCubeAverage L k U j
            (u : (pairedFunctions (Vertex L k 0)).index → ComplexMatrix2)) ∧
      PairedFunctionSpace.PreservesFiniteSupport T ∧
      ∀ g : (pairedFunctions (Vertex L k j)).complexSubmodule,
        (T (PairedFunctionSpace.transposeMap T g) :
            (pairedFunctions (Vertex L k j)).index → ComplexMatrix2) =
          (PeriodicLattice.inverseFourthPowerWeight L ^ j : ℂ) •
            (g : (pairedFunctions (Vertex L k j)).index → ComplexMatrix2) := by
  have hH : ∀ m n : ℕ, m ≤ k → n ≤ k →
      LeftChartFields.HasUniqueTranspose (pairedFunctions (Vertex L k m))
        (pairedFunctions (Vertex L k n)) :=
    fun m n hm hn => hasUniqueTranspose_of_univ
      ((hP.2.2 L k 0 hL (Nat.zero_le k)).2.2 (.vertices m hm univ) (.vertices n hn univ))
  induction j with
  | zero =>
    have s := (transposeMap_spec (hH 0 0 (Nat.zero_le k) (Nat.zero_le k)) LinearMap.id
      fun _ h => h).2 (fun g => g) fun _ _ _ => rfl
    refine ⟨LinearMap.id, fun _ => rfl, fun _ h => h, fun g => ?_⟩
    rw [pow_zero, one_smul]
    exact congrArg Subtype.val (congrFun s g).symm
  | succ j ih =>
    have hjk : j < k := hj
    obtain ⟨T, hv, hc, ht⟩ := ih hjk.le
    obtain ⟨S, sv, sc, st⟩ := hA L hL k j hjk _ (hU.2 j hjk)
    have s₁ := (transposeMap_spec (hH 0 j (Nat.zero_le k) hjk.le) T hc).1
    have s₂ := (transposeMap_spec (hH j (j + 1) hjk.le hj) S sc).1
    have hc' : PairedFunctionSpace.PreservesFiniteSupport (S ∘ₗ T) := fun f hf => sc _ (hc f hf)
    have hcomp := (transposeMap_spec (hH 0 (j + 1) (Nat.zero_le k) hj) (S ∘ₗ T) hc').2
      (fun g => PairedFunctionSpace.transposeMap T (PairedFunctionSpace.transposeMap S g))
      fun g f hf => (s₁ _ f hf).trans (s₂ g (T f) (hc f hf))
    refine ⟨S ∘ₗ T, fun u => ?_, hc', fun g => ?_⟩
    · change (S (T u)).val = adjointCubeAverage (complexIter L k j U)
        (iterAdjointCubeAverage L k U j u.val)
      rw [sv, ← hv]
    · have H1 : T (PairedFunctionSpace.transposeMap T (PairedFunctionSpace.transposeMap S g)) =
          (PeriodicLattice.inverseFourthPowerWeight L ^ j : ℂ) •
            PairedFunctionSpace.transposeMap S g :=
        Subtype.ext (ht _)
      have H2 : (S ∘ₗ T) (PairedFunctionSpace.transposeMap (S ∘ₗ T) g) =
          (PeriodicLattice.inverseFourthPowerWeight L ^ j : ℂ) •
            S (PairedFunctionSpace.transposeMap S g) := by
        rw [← congrFun hcomp g, LinearMap.comp_apply, H1, map_smul]
      rw [H2, pow_succ, mul_smul]
      exact congrArg (fun X => (PeriodicLattice.inverseFourthPowerWeight L ^ j : ℂ) • X) (st g)
theorem covariantIterRelations (hC : ComplexIterChain) (hR : CovariantStepRelations)
    (hN : CovariantStepComplexLinear)
    (hA : CubeAverageMulTranspose.Statement)
    (hP : LeftChartFields.Claim) : CovariantIterRelations := by
  intro L hL k j hj U hU
  exact ⟨fun A hA' => iterCovariantDeriv_eq hC hR hN hL hU hA' j hj,
    fun u hu => ⟨iterAdjointCubeAverage_eq hC hR hN hL hU hu j hj,
      iterCovariantDeriv_covDiff hR hN hL hU hu j hj⟩,
    iterAdjointCubeAverage_mul_transpose hP hA hL hU j hj⟩
end YangMills.Construction.Tower.FullSpace.CovariantIterRelationsProof
end
