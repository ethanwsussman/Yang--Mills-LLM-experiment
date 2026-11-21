import YangMills.Construction.ReflectionPositivity.SequencesOfLatticeDataAndTheirLimits
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient
def toLimitAmbient : Ambient → LimitSpaces.Ambient
  | torus => .periodic
  | euclidean => .euclidean
variable (D : MirrorData)
def listOfSepTuple : (E : Ambient) → {n : ℕ} →
    (toLimitAmbient E).SepTupleUniv D.toStandingParameters .cOne n → FnList D E
  | torus, _, X => List.ofFn X.1
  | euclidean, _, X => List.ofFn X.1
theorem listOfSepTuple_mem_separatedN (E : Ambient) {n : ℕ}
    (X : (toLimitAmbient E).SepTupleUniv D.toStandingParameters .cOne n) :
    listOfSepTuple D E X ∈ separatedN D E n := by
  cases E with
  | torus =>
    refine ⟨List.length_ofFn, ?_, ?_⟩
    · intro g hg
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
      exact X.2.2 i
    · refine List.pairwise_ofFn.2 fun i j hij => X.2.1.2 hij.ne
  | euclidean =>
    refine ⟨List.length_ofFn, ?_, ?_⟩
    · intro g hg
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
      exact X.2.2 i
    · refine List.pairwise_ofFn.2 fun i j hij => X.2.1.2 hij.ne
def restrictToSepTuples (E : Ambient) {n : ℕ} (φ : separatedN D E n → ℝ) :
    (toLimitAmbient E).SepTupleUniv D.toStandingParameters .cOne n → ℝ :=
  fun X => φ ⟨listOfSepTuple D E X, listOfSepTuple_mem_separatedN D E X⟩
variable {D} {E : Ambient}
theorem isSeparatedList_of_mem_separatedAll {X : FnList D E} (hX : X ∈ separatedAll D E) :
    IsSeparatedList D E X := by
  obtain ⟨n, hn⟩ := mem_iUnion.1 hX
  exact hn.2
namespace FunctionalFamily
def CenteredExpansion (T : FunctionalFamily D E) : Prop :=
  (∀ X : separatedAll D E, T.centeredFunctional X =
    ∑ π ∈ (SetPartition.nonSingletonPartitions X.1.length).attach, ∏ J ∈ π.1.parts.attach,
      T J.1.card (LimitSpaces.Ambient.two_le_card_of_mem_nonSingleton π J)
        ⟨subList X.1 J.1,
          subList_mem_separatedN (isSeparatedList_of_mem_separatedAll X.2) J.1⟩) ∧
  T.centeredFunctional (emptyList D E) = 1 ∧
  ∀ X : separatedAll D E, X.1.length = 1 → T.centeredFunctional X = 0
def MultilinearSymmetric (T : FunctionalFamily D E) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n),
    (toLimitAmbient E).IsMultilinearOn D.toStandingParameters (restrictToSepTuples D E (T n hn)) ∧
      (toLimitAmbient E).IsPermInvariant D.toStandingParameters (restrictToSepTuples D E (T n hn))
end FunctionalFamily
namespace LatticeDataSeq
def CenteredConverges (S : LatticeDataSeq D E) (T : FunctionalFamily D E) : Prop :=
  ∀ X : separatedAll D E,
    Tendsto (fun j => S.centredAt j X.1) atTop (𝓝 (T.centeredFunctional X))
section Lip
variable (S : LatticeDataSeq D torus)
def connectedAtLip {n : ℕ}
    (f : LimitSpaces.Ambient.periodic.SepTupleUniv D.toStandingParameters .lip n) (j : ℕ+) : ℂ :=
  SchwingerFunctions.connectedSchwinger D.L D.m (S.K j) (S.β j) f.1
def LipLimitsExist : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    ∀ f : LimitSpaces.Ambient.periodic.SepTupleUniv D.toStandingParameters .lip n,
      ∃ r : ℝ, Tendsto (S.connectedAtLip f) atTop (𝓝 (r : ℂ))
def lipLimitFamily :
    LimitSpaces.Ambient.periodic.TupleFunctionals D.toStandingParameters .lip univ :=
  fun _ _ f => (limUnder atTop (S.connectedAtLip f)).re
def CenteredConvergesOnLip : Prop :=
  ∀ (X : FnList D torus) (hX : IsSepLipList D torus X),
    Tendsto (fun j => S.centredAt j X) atTop
      (𝓝 (LimitSpaces.Ambient.periodic.centredSum D.toStandingParameters S.lipLimitFamily
        ⟨X.get, hX⟩))
end Lip
def CenteredFunctionalsConverge : Prop :=
  (∀ (D : MirrorData) (E : Ambient) (S : LatticeDataSeq D E) (T : FunctionalFamily D E),
    S.TendsToFamily T →
      (S.CenteredConverges T ∧ T.CenteredExpansion) ∧
        T.MultilinearSymmetric) ∧
  ∀ (D : MirrorData) (S : LatticeDataSeq D torus) (T : FunctionalFamily D torus),
    S.TendsToFamily T → S.LipLimitsExist → S.CenteredConvergesOnLip
end LatticeDataSeq
end YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient
end
