import YangMills.Construction.Continuum.TwoScalesOfClassesOfTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusTransport.TupleVectors.TwoScaleMembership
variable (D : TransportData)
def MotionsPreserveTuples : Prop :=
  ∀ (s : (Fin 4 → ℝ) → Fin 4 → ℝ) (hs : IsEuclideanMotion s),
    ∀ t ∈ sepTuples D Set.univ,
      (∀ i, familyAct hs t.2 i = t.2 i ∘ hs.toPerm.symm) ∧
      actAny hs t ∈ sepTuples D Set.univ ∧
      (∀ i, entrySupp D (familyAct hs t.2 i) = s '' entrySupp D (t.2 i)) ∧
      (∀ i, IsCompact (s '' entrySupp D (t.2 i))) ∧
      Pairwise fun i k => Disjoint (s '' entrySupp D (t.2 i)) (s '' entrySupp D (t.2 k))
def ReflectionsAreInvolutive : Prop :=
  ∀ (u : Fin 4 → ℝ) (c : ℝ), euclidNorm u = 1 →
    ∀ ρ : (Fin 4 → ℝ) → Fin 4 → ℝ, (∀ x, ρ x = x - (2 * (scalarProd u x - c)) • u) →
      ∃ hρ : IsEuclideanMotion ρ, hρ.toPerm.symm = hρ.toPerm ∧
        ∀ t ∈ sepTuples D Set.univ,
          actAny hρ t = compAny t ρ
def ExistsAdmissibleClass : Prop :=
  ∀ t ∈ sepTuples D Set.univ,
    ∃ (d R : ℝ) (hd : 0 < d) (hR : 0 < R), t ∈ admissibleSepTuples D d R hd hR
def CubeClassSubsetAdmissible : Prop :=
  ∀ (ϖ d R : ℝ) (hϖ : 0 < ϖ) (hd : 0 < d) (hR : 0 < R),
    cubeSepTuples D ϖ d R hϖ hd hR ⊆ admissibleSepTuples D d R hd hR ∧
    ∀ t ∈ cubeSepTuples D ϖ d R hϖ hd hR,
      ∀ i, entrySupp D (t.2 i) ⊆ {x | maxNorm x < ϖ - d / 2}
def FiniteSetsInCommonCubeClass : Prop :=
  ∀ T : Set FnTuple, T.Finite → T ⊆ sepTuples D Set.univ →
    ∃ (ϖ : ℕ+) (d R : ℝ) (hϖ : 0 < ((ϖ : ℕ) : ℝ)) (hd : 0 < d) (hR : 0 < R),
      T ⊆ cubeSepTuples D ((ϖ : ℕ) : ℝ) d R hϖ hd hR ∧
      (∀ k : ℕ+, ∃ z : ℤ, ((ϖ : ℕ) : ℝ) = (D.L : ℝ) ^ (-((k : ℕ) : ℤ)) * (z : ℝ)) ∧
      (∃ z : ℤ, ((ϖ : ℕ) : ℝ) = D.spacing * (z : ℝ)) ∧
      d ≤ 1
def Statement : Prop :=
  ∀ D : TransportData,
    MotionsPreserveTuples D ∧ ReflectionsAreInvolutive D ∧
    ExistsAdmissibleClass D ∧ CubeClassSubsetAdmissible D ∧
    FiniteSetsInCommonCubeClass D
end YangMills.Construction.TorusTransport.TupleVectors.TwoScaleMembership
end
