import YangMills.Construction.ToriAtArbitraryCouplings.BoundFunctionsAndTheFamiliesThatObeyThem
import YangMills.Construction.ToriAtArbitraryCouplings.TheVectorSpacesOfClassC1AndTheNeighbourhoodsAtASide
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
def lipschitzCompactSupportSubmodule {X : Type*} [MetricSpace X] (A : Set X) :
    Submodule ℝ (X → ℝ) where
  carrier := {f | TestFunctions.IsLipschitzFor (dist : X → X → ℝ) f ∧ IsCompact (tsupport f) ∧
    tsupport f ⊆ A}
  zero_mem' := by
    have hz : tsupport (0 : X → ℝ) = ∅ := by simp [tsupport]
    exact ⟨⟨0, le_rfl, fun x y => by simp⟩, by simp [hz], by simp [hz]⟩
  add_mem' := by
    rintro f g ⟨⟨K, hK, hf⟩, cf, sf⟩ ⟨⟨K', hK', hg⟩, cg, sg⟩
    have hsub : tsupport (f + g) ⊆ tsupport f ∪ tsupport g :=
      closure_minimal
        ((Function.support_add f g).trans
          (Set.union_subset_union (subset_tsupport f) (subset_tsupport g)))
        ((isClosed_tsupport f).union (isClosed_tsupport g))
    refine ⟨⟨K + K', add_nonneg hK hK', fun x y => ?_⟩,
      (cf.union cg).of_isClosed_subset (isClosed_tsupport _) hsub,
      hsub.trans (Set.union_subset sf sg)⟩
    calc ‖(f + g) x - (f + g) y‖ = ‖(f x - f y) + (g x - g y)‖ := by
          simp only [Pi.add_apply]
          congr 1
          ring
      _ ≤ ‖f x - f y‖ + ‖g x - g y‖ := norm_add_le _ _
      _ ≤ _ := by
          rw [add_mul]
          exact add_le_add (hf x y) (hg x y)
  smul_mem' := by
    rintro a f ⟨⟨K, hK, hf⟩, cf, sf⟩
    have hsub : tsupport (a • f) ⊆ tsupport f :=
      closure_mono (Function.support_const_smul_subset a f)
    refine ⟨⟨|a| * K, mul_nonneg (abs_nonneg a) hK, fun x y => ?_⟩,
      cf.of_isClosed_subset (isClosed_tsupport _) hsub, hsub.trans sf⟩
    calc ‖(a • f) x - (a • f) y‖ = |a| * ‖f x - f y‖ := by
          simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, norm_mul, Real.norm_eq_abs]
      _ ≤ |a| * (K * dist x y) := mul_le_mul_of_nonneg_left (hf x y) (abs_nonneg a)
      _ = _ := by ring
theorem mem_lipschitzCompactSupportSubmodule_iff {X : Type*} [MetricSpace X] (A : Set X)
    (f : X → ℝ) :
    f ∈ lipschitzCompactSupportSubmodule A ↔
      TestFunctions.IsLipschitzFor (dist : X → X → ℝ) f ∧
        MetricNotions.IsCompactWrt (dist : X → X → ℝ)
          (MetricNotions.closureWrt (dist : X → X → ℝ) {x | f x ≠ 0}) ∧
        MetricNotions.closureWrt (dist : X → X → ℝ) {x | f x ≠ 0} ⊆ A := by
  rw [← AmbientPoints.closure_eq_closureWrt, ← AmbientPoints.isCompact_iff_isCompactWrt]
  rfl
namespace TorusSide
variable (s : TorusSide)
def lipSubmodule : (E : Ambient) → Set (s.Point E) → Submodule ℝ (s.Point E → ℝ)
  | .torus, A => lipschitzCompactSupportSubmodule
      (X := AmbientPoints.Pt s.asMirrorData.toStandingParameters .torus) A
  | .euclidean, A => lipschitzCompactSupportSubmodule
      (X := AmbientPoints.Pt s.asMirrorData.toStandingParameters .euclidean) A
theorem mem_lipSubmodule_iff (E : Ambient) (A : Set (s.Point E)) (f : s.Point E → ℝ) :
    f ∈ s.lipSubmodule E A ↔ f ∈ s.lipSuppIn E A := by
  cases E
  · exact mem_lipschitzCompactSupportSubmodule_iff
      (X := AmbientPoints.Pt s.asMirrorData.toStandingParameters .torus) A f
  · exact mem_lipschitzCompactSupportSubmodule_iff
      (X := AmbientPoints.Pt s.asMirrorData.toStandingParameters .euclidean) A f
def SatisfiesTelescopingBound (m' : ℕ) (E : Ambient) {n : ℕ}
    {V : Fin n → Submodule ℝ (s.Point E → ℝ)} (F : ((l : Fin n) → V l) → ℝ) (c : ℝ) : Prop :=
  ∀ f g : (l : Fin n) → V l,
    |F f - F g| ≤
      c * ∑ l, s.sharpNormAt m' E ((f l : s.Point E → ℝ) - (g l : s.Point E → ℝ)) *
        ∏ l' ∈ Finset.univ.erase l,
          (s.sharpNormAt m' E (f l' : s.Point E → ℝ) + s.sharpNormAt m' E (g l' : s.Point E → ℝ))
def BoundedMultilinearSatisfyTelescoping (m' : ℕ) (E : Ambient) {n : ℕ}
    (V : Fin n → Submodule ℝ (s.Point E → ℝ)) (c : ℝ) : Prop :=
  ∀ Ψ : MultilinearMap ℝ (fun l => V l) ℝ,
    (∀ u : (l : Fin n) → V l, |Ψ u| ≤ c * ∏ l, s.sharpNormAt m' E (u l : s.Point E → ℝ)) →
      s.SatisfiesTelescopingBound m' E Ψ c
def componentsAsTuple (E : Ambient) {n : ℕ} {V : Fin n → Submodule ℝ (s.Point E → ℝ)}
    (u : (l : Fin n) → V l) : s.FnTuple E :=
  List.ofFn fun l => (u l : s.Point E → ℝ)
def restrictToProduct (E : Ambient) {n : ℕ} (Ψ : s.sepOfLength E n → ℝ)
    (V : Fin n → Submodule ℝ (s.Point E → ℝ)) (u : (l : Fin n) → V l) : ℝ :=
  Ambient.evalOrZero Ψ (s.componentsAsTuple E u)
end TorusSide
namespace TelescopingEquicontinuity
def MultilinearTelescopingBound : Prop :=
  ∀ n : ℕ, 1 ≤ n →
  ∀ (V : Fin n → Type) [∀ l, AddCommGroup (V l)] [∀ l, Module ℝ (V l)]
    (p : ∀ l, Seminorm ℝ (V l)) (c : ℝ), 0 ≤ c →
  ∀ Ψ : MultilinearMap ℝ V ℝ,
    (∀ u : ∀ l, V l, |Ψ u| ≤ c * ∏ l, p l (u l)) →
  ∀ f g : ∀ l, V l,
    |Ψ f - Ψ g| ≤
      c * ∑ l, p l (f l - g l) * (∏ l' ∈ Finset.Iio l, p l' (g l')) *
        ∏ l' ∈ Finset.Ioi l, p l' (f l')
def PairwiseSeparatedBy (s : TorusSide) (E : Ambient) {n : ℕ} (d : ℝ)
    (A : Fin n → Set (s.Point E)) : Prop :=
  ∀ i k, i ≠ k → ENNReal.ofReal d ≤ s.setDist E (A i) (A k)
def ConnectedFamiliesTelescope (s : TorusSide) (m' : ℕ) (E : Ambient) {n : ℕ} (hn : 2 ≤ n)
    (d : ℝ) (A : Fin n → Set (s.Point E)) : Prop :=
  ∀ (C : Schwinger.ClusterBound) (S : Ambient.ConnectedFamily s.asMirrorData E),
    s.SatisfiesClusterBound m' C E S → ∀ R ∈ s.admissibleRadiusSet E,
      (∀ l, ∃ B, s.IsBallWithRadius E B R ∧ A l ⊆ B) →
        (∀ u : (l : Fin n) → s.c1Submodule E (A l),
          s.componentsAsTuple E u ∈ s.sepOfLength E n) ∧
        s.SatisfiesTelescopingBound m' E
          (s.restrictToProduct E (S.fn n hn) fun l => s.c1Submodule E (A l)) (C.value n d R)
def Claim : Prop :=
  MultilinearTelescopingBound ∧
    ∀ (s : TorusSide), 8 * 105 ^ 4 ≤ s.L → ∀ (m' : ℕ) (E : Ambient) (n : ℕ) (hn : 2 ≤ n) (d : ℝ),
      0 < d →
      ∀ A : Fin n → Set (s.Point E), PairwiseSeparatedBy s E d A →
        (∀ c : ℝ, 0 ≤ c →
          s.BoundedMultilinearSatisfyTelescoping m' E (fun l => s.lipSubmodule E (A l)) c ∧
            s.BoundedMultilinearSatisfyTelescoping m' E (fun l => s.c1Submodule E (A l)) c) ∧
          ConnectedFamiliesTelescope s m' E hn d A
end TelescopingEquicontinuity
end YangMills.Construction.ToriAtArbitraryCouplings
end
