import YangMills.Construction.Continuum.ClassesOfTuples
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TorusTransport.SupportFacts
variable (D : TransportData)
def NbhdDistLowerBound : Prop :=
  ∀ (S S' : Set (Fin 4 → ℝ)) (η η' : ℝ), IsCompact S → IsCompact S' → 0 < η → 0 < η' →
    Domain.euclidean.setDist D S S' - ENNReal.ofReal η - ENNReal.ofReal η' ≤
        Domain.euclidean.setDist D (closedNbhd S η) (closedNbhd S' η') ∧
      (S = ∅ ∨ S' = ∅ →
        Domain.euclidean.setDist D (closedNbhd S η) (closedNbhd S' η') = ∞ ∧
          Domain.euclidean.setDist D S S' - ENNReal.ofReal η - ENNReal.ofReal η' = ∞)
def SubfamilyIsAdmissible : Prop :=
  ∀ (q : ℕ+) (d R : ℝ) (hd : 0 < d) (hR : 0 < R) (A : Fin q → Set (Fin 4 → ℝ)),
    IsAdmissibleSets D d R hd hR A →
      ∀ (J : Finset (Fin q)) (hJ : J.Nonempty),
        IsAdmissibleSets D d R hd hR (subfamily A J hJ)
def AdmissibleProductMembers : Prop :=
  ∀ (q : ℕ+) (d R : ℝ) (hd : 0 < d) (hR : 0 < R) (A : Fin q → Set (Fin 4 → ℝ)),
    IsAdmissibleSets D d R hd hR A →
      ∀ h : Domain.euclidean.FnFamily D q ℝ,
        (∀ l, h l ∈ lipschitzSupportedIn (A l)) →
          Domain.euclidean.IsSepLipschitz D h ∧
            Domain.euclidean.IsBallSupported D R hR h ∧
            (∀ l k, l ≠ k → ENNReal.ofReal d ≤
              Domain.euclidean.setDist D (Domain.euclidean.fnSupport D (h l))
                (Domain.euclidean.fnSupport D (h k))) ∧
            h ∈ Domain.euclidean.lipFamilies D q d R hd hR trivial ∧
            ∀ (hq : 2 ≤ (q : ℕ)) (hs : Domain.euclidean.IsSepLipschitz D h),
              ENNReal.ofReal d ≤ Domain.euclidean.supportGap D hq h hs
def LipFamilyIsSepLipschitz : Prop :=
  ∀ (n : ℕ+) (d R : ℝ) (hd : 0 < d) (hR : 0 < R) (f : Domain.euclidean.FnFamily D n ℝ),
    f ∈ Domain.euclidean.lipFamilies D n d R hd hR trivial →
      Domain.euclidean.IsSepLipschitz D f
def C1CompactIsLipschitz : Prop :=
  ∀ f : RealFun (Fin 4 → ℝ), RealFun.toComplex f ∈ c1CompactSupport →
    Domain.euclidean.gradSupNorm D f < ∞ ∧
      (∀ x y : Fin 4 → ℝ,
        |f x - f y| ≤ (Domain.euclidean.gradSupNorm D f).toReal * euclidNorm (x - y)) ∧
      Domain.euclidean.lipConst D f ≤ Domain.euclidean.gradSupNorm D f
def DisjointC1FamilyIsSeparated : Prop :=
  ∀ (n : ℕ+) (f : Domain.euclidean.FnFamily D n ℝ),
    (∀ i, RealFun.toComplex (f i) ∈ c1CompactSupport) →
      (∀ i k, i ≠ k →
        Disjoint (Domain.euclidean.fnSupport D (f i)) (Domain.euclidean.fnSupport D (f k))) →
        Domain.euclidean.IsSepLipschitz D f ∧ f ∈ Domain.euclidean.sepC1Families D n
def SupportedFnSubmodules : Prop :=
  ∀ A : Set (Fin 4 → ℝ),
    (∃ V : Submodule ℝ (RealFun (Fin 4 → ℝ)),
      (V : Set (RealFun (Fin 4 → ℝ))) = lipschitzSupportedIn A) ∧
    (∃ V : Submodule ℝ (RealFun (Fin 4 → ℝ)),
      (V : Set (RealFun (Fin 4 → ℝ))) = c1SupportedIn A) ∧
    c1SupportedIn A ⊆ lipschitzSupportedIn A
def DisjointIffPosDist : Prop :=
  (∀ S S' : Set (Fin 4 → ℝ), IsCompact S → IsCompact S' → Disjoint S S' →
    0 < Domain.euclidean.setDist D S S') ∧
  ∀ S S' : Set (Fin 4 → ℝ), 0 < Domain.euclidean.setDist D S S' → Disjoint S S'
def AllSupportFacts : Prop :=
  ∀ D : TransportData,
    NbhdDistLowerBound D ∧
    SubfamilyIsAdmissible D ∧
    AdmissibleProductMembers D ∧
    LipFamilyIsSepLipschitz D ∧
    C1CompactIsLipschitz D ∧
    DisjointC1FamilyIsSeparated D ∧
    SupportedFnSubmodules ∧
    DisjointIffPosDist D
end YangMills.Construction.TorusTransport.SupportFacts
end
