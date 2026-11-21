import YangMills.Construction.Towers.CovariantDifferenceRelationsOfAStepOfASide
import YangMills.Construction.Towers.GaugeCovarianceOfTheCovariantAveragesOnTheSidesProof
import YangMills.Construction.Towers.LinearityOfTheCovariantMapsOfAStepOnTheSides
import YangMills.Construction.Towers.ProductOfTheBlockAverageWithItsTransposeOnTheSides
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.IterRelationsProof
open LeftChartFields PairedFunctionSpace
section Transposes
theorem mem_complexSubmodule_iff {X : Type} {f : X → Matrices.ComplexMatrix2} :
    f ∈ (pairedFunctions X).complexSubmodule ↔ ∀ x, f x ∈ Matrices.ComplexMatrix2.traceless := by
  show f ∈ Matrices.GroupLieProduct.tracelessFunctions X ↔ _
  simp [Matrices.GroupLieProduct.tracelessFunctions, Submodule.mem_pi]
def toUnivFunctions (X : Type) :
    (pairedFunctions X).complexSubmodule →ₗ[ℂ]
      (pairedFunctions ↥(univ : Set X)).complexSubmodule where
  toFun f := ⟨fun x => f.1 x.1,
    mem_complexSubmodule_iff.2 fun x => mem_complexSubmodule_iff.1 f.2 x.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def ofUnivFunctions (X : Type) :
    (pairedFunctions ↥(univ : Set X)).complexSubmodule →ₗ[ℂ]
      (pairedFunctions X).complexSubmodule where
  toFun f := ⟨fun x => f.1 ⟨x, mem_univ x⟩,
    mem_complexSubmodule_iff.2 fun x => mem_complexSubmodule_iff.1 f.2 ⟨x, mem_univ x⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem pair_toUnivFunctions {X : Type} (f f' : (pairedFunctions X).complexSubmodule) :
    (pairedFunctions ↥(univ : Set X)).pair (toUnivFunctions X f) (toUnivFunctions X f') =
      (pairedFunctions X).pair f f' :=
  finsum_comp_equiv (Equiv.Set.univ X)
    (f := fun x => Matrices.ComplexMatrix2.halfTrace (f.1 x * f'.1 x))
theorem hasFiniteSupp_comp {α β : Type} {e : α → β} (he : Function.Injective e)
    {f : β → Matrices.ComplexMatrix2}
    (hf : HasFiniteSupp f) : HasFiniteSupp (fun x => f (e x)) :=
  Set.Finite.subset (Set.Finite.preimage he.injOn hf) fun _ hx => hx
theorem isFinitelySupported_toUniv {X : Type} {f : (pairedFunctions X).complexSubmodule}
    (hf : (pairedFunctions X).IsFinitelySupported f) :
    (pairedFunctions ↥(univ : Set X)).IsFinitelySupported (toUnivFunctions X f) :=
  hasFiniteSupp_comp (e := (Subtype.val : ↥(univ : Set X) → X)) Subtype.val_injective hf
theorem isFinitelySupported_ofUniv {X : Type}
    {f : (pairedFunctions ↥(univ : Set X)).complexSubmodule}
    (hf : (pairedFunctions ↥(univ : Set X)).IsFinitelySupported f) :
    (pairedFunctions X).IsFinitelySupported (ofUnivFunctions X f) :=
  hasFiniteSupp_comp (e := fun x : X => (⟨x, mem_univ x⟩ : ↥(univ : Set X)))
    (fun _ _ h => congrArg Subtype.val h) hf
theorem transposeMap_spec {X Y : Type}
    (h : HasUniqueTranspose (pairedFunctions ↥(univ : Set X))
      (pairedFunctions ↥(univ : Set Y)))
    (T : (pairedFunctions X).complexSubmodule →ₗ[ℂ] (pairedFunctions Y).complexSubmodule)
    (hT : PreservesFiniteSupport T) :
    IsTransposeMap T (transposeMap T) ∧ ∀ R, IsTransposeMap T R → R = transposeMap T := by
  obtain ⟨T', hT', huniq⟩ := h ((toUnivFunctions Y).comp (T.comp (ofUnivFunctions X)))
    (fun f hf => isFinitelySupported_toUniv (hT _ (isFinitelySupported_ofUniv hf)))
  have hR : IsTransposeMap T ((ofUnivFunctions X).comp (T'.comp (toUnivFunctions Y))) := by
    intro g f hf
    have e := hT' (toUnivFunctions Y g) (toUnivFunctions X f) (isFinitelySupported_toUniv hf)
    calc (pairedFunctions X).pair (ofUnivFunctions X (T' (toUnivFunctions Y g))) f
        = (pairedFunctions ↥(univ : Set X)).pair (T' (toUnivFunctions Y g))
            (toUnivFunctions X f) :=
          (pair_toUnivFunctions (ofUnivFunctions X (T' (toUnivFunctions Y g))) f).symm
      _ = (pairedFunctions ↥(univ : Set Y)).pair (toUnivFunctions Y g)
            (toUnivFunctions Y (T f)) := e
      _ = (pairedFunctions Y).pair g (T f) := pair_toUnivFunctions g (T f)
  have hone : ∀ R, IsTransposeMap T R →
      R = (ofUnivFunctions X).comp (T'.comp (toUnivFunctions Y)) := by
    intro R hR'
    have e : (fun g => toUnivFunctions X (R (ofUnivFunctions Y g))) = T' := by
      refine huniq _ fun g f hf => ?_
      calc (pairedFunctions ↥(univ : Set X)).pair (toUnivFunctions X (R (ofUnivFunctions Y g))) f
          = (pairedFunctions ↥(univ : Set X)).pair (toUnivFunctions X (R (ofUnivFunctions Y g)))
              (toUnivFunctions X (ofUnivFunctions X f)) := rfl
        _ = (pairedFunctions X).pair (R (ofUnivFunctions Y g)) (ofUnivFunctions X f) :=
            pair_toUnivFunctions _ _
        _ = (pairedFunctions Y).pair (ofUnivFunctions Y g) (T (ofUnivFunctions X f)) :=
            hR' _ _ (isFinitelySupported_ofUniv hf)
        _ = (pairedFunctions ↥(univ : Set Y)).pair (toUnivFunctions Y (ofUnivFunctions Y g))
              (toUnivFunctions Y (T (ofUnivFunctions X f))) := (pair_toUnivFunctions _ _).symm
    refine LinearMap.ext fun g => ?_
    show R g = ofUnivFunctions X (T' (toUnivFunctions Y g))
    rw [← e]
    rfl
  have hspec : IsTransposeMap T (transposeMap T) := Classical.epsilon_spec ⟨_, hR⟩
  exact ⟨hspec, fun R hR' => (hone R hR').trans (hone _ hspec).symm⟩
theorem transposeMap_comp {P P' P'' : PairedFunctionSpace}
    (T : P.complexSubmodule →ₗ[ℂ] P'.complexSubmodule)
    (S : P'.complexSubmodule →ₗ[ℂ] P''.complexSubmodule) (hc : PreservesFiniteSupport T)
    (hT : IsTransposeMap T (transposeMap T)) (hS : IsTransposeMap S (transposeMap S))
    (hu : ∀ R, IsTransposeMap (S.comp T) R → R = transposeMap (S.comp T)) :
    transposeMap (S.comp T) = (transposeMap T).comp (transposeMap S) :=
  (hu _ fun g f hf => (hT _ f hf).trans (hS g _ (hc f hf))).symm
end Transposes
section Restrictions
variable {L n k : ℕ}
theorem restrictVertexFunction_zero (hL : 0 < L) (l : Vertex L n k 0 → Matrices.ComplexMatrix2) :
    restrictVertexFunction 0 l = l := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.restrictVertexFunction_zero <;> assumption
theorem restrictVertexFunction_succ_restrict (hL : 0 < L) {i : ℕ}
    (l : Vertex L n k 0 → Matrices.ComplexMatrix2) :
    restrictVertexFunction (i + 1) (restrictVertexFunction i l) =
      restrictVertexFunction (i + 1) l := by apply _root_.YangMills.Construction.Tower.GaugeCovarianceProof.restrictVertexFunction_succ <;> assumption
theorem covDiff_add {i : ℕ} (V : Edge L n k i → Matrices.ComplexMatrix2)
    (a b : Vertex L n k i → Matrices.ComplexMatrix2) :
    covDiff V (a + b) = covDiff V a + covDiff V b := by
  funext c
  simp only [covDiff, extendOddly, Pi.add_apply, Matrices.ComplexMatrix2.conjugateBy, mul_add,
    add_mul]
  split_ifs <;> abel
theorem covDiff_zero {i : ℕ} (V : Edge L n k i → Matrices.ComplexMatrix2) :
    covDiff V (0 : Vertex L n k i → Matrices.ComplexMatrix2) = 0 := by
  funext c
  simp only [covDiff, extendOddly, Pi.zero_apply, Matrices.ComplexMatrix2.conjugateBy, mul_zero,
    zero_mul, sub_zero, neg_zero, ite_self]
end Restrictions
theorem covariantIterRelations_holds (hChain : ComplexIterDerivChain)
    (hRel : CovDiffStepRelations)
    (hLin : StepMapsComplexLinear.Claim)
    (hProd : AdjointCubeAverageMulTranspose)
    (hChart : LeftChartFields.Claim) :
    CovariantIterRelations := by
  intro L hL n k j hn hj U hU
  have hL0 : 0 < L := by have := hL.2; omega
  have hV : ∀ i < k, PeriodicLattice.complexBlockFieldAtLevel i U ∈ smallComplexFields L n k i :=
    hU.2
  have hsuccV : ∀ i, (PeriodicLattice.complexBlockFieldAtLevel (i + 1) U :
      Edge L n k (i + 1) → Matrices.ComplexMatrix2) =
      PeriodicLattice.complexBlockAverageStep i (PeriodicLattice.complexBlockFieldAtLevel i U) :=
    fun _ => rfl
  have hzeroV : (PeriodicLattice.complexBlockFieldAtLevel 0 U :
      Edge L n k 0 → Matrices.ComplexMatrix2) = U := rfl
  have hDrift : ∀ i ≤ k, ∀ B ∈ complexEdgeForms L n k 0, ∀ y,
      iterContourLogDrift L n k U i B y ∈ Matrices.ComplexMatrix2.traceless := by
    intro i
    induction i with
    | zero => intro _ B _ y; exact Matrices.ComplexMatrix2.traceless.zero_mem
    | succ i ih =>
      intro hi B hB y
      have hi' : i < k := hi
      have hl := hLin L hL n k i hn hi' _ (hV i hi')
      have hq := (hChain L hL n k hn U hU B hB).2.2 i hi'.le
      exact Matrices.ComplexMatrix2.traceless.add_mem ((hl.2.2.1 _ (ih hi'.le B hB)).2 y)
        ((hl.1 _ hq).2 y)
  have hAverage : ∀ i ≤ k, ∀ l : Vertex L n k 0 → Matrices.ComplexMatrix2,
      (∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) → ∀ y,
      iterAdjointCubeAverage L n k U i l y ∈ Matrices.ComplexMatrix2.traceless := by
    intro i
    induction i with
    | zero => intro _ l hl y; exact hl y
    | succ i ih =>
      intro hi l hl y
      have hi' : i < k := hi
      exact ((hLin L hL n k i hn hi' _ (hV i hi')).2.2.1 _ (ih hi'.le l hl)).2 y
  have hFirst : ∀ i ≤ k, ∀ B ∈ complexEdgeForms L n k 0,
      iterCovariantDeriv L n k U i B =
        complexIterDeriv L n k i U B +
          covDiff (PeriodicLattice.complexBlockFieldAtLevel i U)
            (iterContourLogDrift L n k U i B) := by
    intro i
    induction i with
    | zero =>
      intro _ B hB
      show B = complexIterDeriv L n k 0 U B + covDiff _ 0
      rw [(hChain L hL n k hn U hU B hB).1, covDiff_zero, add_zero]
    | succ i ih =>
      intro hi B hB
      have hi' : i < k := hi
      have hl := hLin L hL n k i hn hi' _ (hV i hi')
      have hs := hDrift i hi'.le B hB
      have hr := hRel L hL n k i hn hi' _ (hV i hi') _ hs
      have hc := hChain L hL n k hn U hU B hB
      have hq := hc.2.2 i hi'.le
      have e := hl.2.1 _ hq _ (hl.2.2.1 _ hs).1 1
      simp only [one_smul] at e
      show covariantSmoothingDeriv (PeriodicLattice.complexBlockFieldAtLevel i U)
          (iterCovariantDeriv L n k U i B) =
        complexIterDeriv L n k (i + 1) U B +
          covDiff (PeriodicLattice.complexBlockFieldAtLevel (i + 1) U)
            (adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel i U)
                (iterContourLogDrift L n k U i B) +
              contourLogDrift (PeriodicLattice.complexBlockFieldAtLevel i U)
                (complexIterDeriv L n k i U B))
      rw [ih hi'.le B hB, hc.2.1 i hi', covariantSmoothingDeriv, e.1, e.2, hr.1, hr.2.1,
        hsuccV, add_assoc, ← covDiff_add]
      congr 2
      abel
  have hForm : 0 < k → ∀ l : Vertex L n k 0 → Matrices.ComplexMatrix2,
      (∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) →
      covDiff U l ∈ complexEdgeForms L n k 0 := fun hk l hl =>
    ((hLin L hL n k 0 hn hk _ (hV 0 hk)).2.2.1 l hl).1
  have hQD : 0 < k → ∀ i ≤ k, ∀ l : Vertex L n k 0 → Matrices.ComplexMatrix2,
      (∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) →
      complexIterDeriv L n k i U (covDiff U l) =
        covDiff (PeriodicLattice.complexBlockFieldAtLevel i U) (restrictVertexFunction i l) := by
    intro hk i
    induction i with
    | zero =>
      intro _ l hl
      rw [(hChain L hL n k hn U hU _ (hForm hk l hl)).1, restrictVertexFunction_zero hL0, hzeroV]
    | succ i ih =>
      intro hi l hl
      have hi' : i < k := hi
      rw [(hChain L hL n k hn U hU _ (hForm hk l hl)).2.1 i hi', ih hi'.le l hl,
        (hRel L hL n k i hn hi' _ (hV i hi') (restrictVertexFunction i l) fun x => hl _).1,
        restrictVertexFunction_succ_restrict hL0, hsuccV]
  have hSecond : ∀ i ≤ k, ∀ l : Vertex L n k 0 → Matrices.ComplexMatrix2,
      (∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) →
      iterAdjointCubeAverage L n k U i l =
          restrictVertexFunction i l + iterContourLogDrift L n k U i (covDiff U l) ∧
        iterCovariantDeriv L n k U i (covDiff U l) =
          covDiff (PeriodicLattice.complexBlockFieldAtLevel i U)
            (iterAdjointCubeAverage L n k U i l) := by
    intro i
    induction i with
    | zero =>
      intro _ l _
      refine ⟨?_, rfl⟩
      show l = restrictVertexFunction 0 l + 0
      rw [restrictVertexFunction_zero hL0, add_zero]
    | succ i ih =>
      intro hi l hl
      have hi' : i < k := hi
      have hk : 0 < k := by omega
      have hlin := hLin L hL n k i hn hi' _ (hV i hi')
      have hs := hDrift i hi'.le _ (hForm hk l hl)
      have hsr : ∀ x, restrictVertexFunction i l x ∈ Matrices.ComplexMatrix2.traceless :=
        fun x => hl _
      have hrr := hRel L hL n k i hn hi' _ (hV i hi') _ hsr
      have e := (hlin.2.2.2 _ _ hsr hs 1).2
      simp only [one_smul] at e
      obtain ⟨h₁, h₂⟩ := ih hi'.le l hl
      refine ⟨?_, ?_⟩
      · show adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel i U)
            (iterAdjointCubeAverage L n k U i l) =
          restrictVertexFunction (i + 1) l +
            (adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel i U)
                (iterContourLogDrift L n k U i (covDiff U l)) +
              contourLogDrift (PeriodicLattice.complexBlockFieldAtLevel i U)
                (complexIterDeriv L n k i U (covDiff U l)))
        rw [h₁, e, hQD hk i hi'.le l hl, hrr.2.1, restrictVertexFunction_succ_restrict hL0]
        abel
      · show covariantSmoothingDeriv (PeriodicLattice.complexBlockFieldAtLevel i U)
            (iterCovariantDeriv L n k U i (covDiff U l)) =
          covDiff (PeriodicLattice.complexBlockFieldAtLevel (i + 1) U)
            (adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel i U)
              (iterAdjointCubeAverage L n k U i l))
        rw [h₂, (hRel L hL n k i hn hi' _ (hV i hi') _ (hAverage i hi'.le l hl)).2.2, hsuccV]
  have hTr : ∀ a ≤ k, ∀ b ≤ k,
      HasUniqueTranspose (pairedFunctions ↥(univ : Set (Vertex L n k a)))
        (pairedFunctions ↥(univ : Set (Vertex L n k b))) := fun a ha b hb =>
    (((hChart.2.2 L k 0 hL (Nat.zero_le k)).1 n hn).2.2
      (FiniteCarrier.vertices a ha univ) (FiniteCarrier.vertices b hb univ)).1
  have hLast : ∀ i ≤ k,
      ∃ T : (pairedFunctions (Vertex L n k 0)).complexSubmodule →ₗ[ℂ]
          (pairedFunctions (Vertex L n k i)).complexSubmodule,
        (∀ l : (pairedFunctions (Vertex L n k 0)).complexSubmodule,
          (T l : (pairedFunctions (Vertex L n k i)).index → Matrices.ComplexMatrix2) =
            iterAdjointCubeAverage L n k U i
              (l : (pairedFunctions (Vertex L n k 0)).index → Matrices.ComplexMatrix2)) ∧
        PreservesFiniteSupport T ∧
        ∀ g : (pairedFunctions (Vertex L n k i)).complexSubmodule,
          (T (transposeMap T g) :
              (pairedFunctions (Vertex L n k i)).index → Matrices.ComplexMatrix2) =
            (PeriodicLattice.inverseFourthPowerWeight L ^ i : ℂ) •
              (g : (pairedFunctions (Vertex L n k i)).index → Matrices.ComplexMatrix2) := by
    intro i
    induction i with
    | zero =>
      intro h0
      refine ⟨LinearMap.id, fun _ => rfl, fun _ h => h, fun g => ?_⟩
      have ht := transposeMap_spec (hTr 0 h0 0 h0) LinearMap.id fun _ h => h
      rw [← ht.2 LinearMap.id fun _ _ _ => rfl]
      simp
    | succ i ih =>
      intro hi
      have hi' : i < k := hi
      obtain ⟨T, hT, hcT, hTT⟩ := ih hi'.le
      obtain ⟨S, hS, hcS, hSS⟩ := hProd L hL n k i hn hi' _ (hV i hi')
      have hcST : PreservesFiniteSupport (S.comp T) := fun f hf => hcS _ (hcT f hf)
      refine ⟨S.comp T, fun l => ?_, hcST, fun g => ?_⟩
      · show ((S (T l) : (pairedFunctions (Vertex L n k (i + 1))).complexSubmodule) :
            (pairedFunctions (Vertex L n k (i + 1))).index → Matrices.ComplexMatrix2) =
          adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel i U)
            (iterAdjointCubeAverage L n k U i l.1)
        rw [hS, hT]
      · rw [transposeMap_comp T S hcT
          (transposeMap_spec (hTr 0 (Nat.zero_le k) i hi'.le) T hcT).1
          (transposeMap_spec (hTr i hi'.le (i + 1) hi) S hcS).1
          (transposeMap_spec (hTr 0 (Nat.zero_le k) (i + 1) hi) (S.comp T) hcST).2]
        have e : T (transposeMap T (transposeMap S g)) =
            (PeriodicLattice.inverseFourthPowerWeight L ^ i : ℂ) • transposeMap S g :=
          Subtype.ext (hTT _)
        show ((S (T (transposeMap T (transposeMap S g))) :
            (pairedFunctions (Vertex L n k (i + 1))).complexSubmodule) :
            (pairedFunctions (Vertex L n k (i + 1))).index → Matrices.ComplexMatrix2) = _
        rw [e, map_smul, Submodule.coe_smul, hSS, smul_smul, pow_succ]
  exact ⟨hFirst j hj, hSecond j hj, hLast j hj⟩
end YangMills.Construction.Tower.IterRelationsProof
end
