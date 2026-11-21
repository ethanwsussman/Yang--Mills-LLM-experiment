import YangMills.Construction.Lattice.ConnectedFunctionsAtArbitraryArguments
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
noncomputable section
namespace YangMills.Construction.AmbientPoints
section MetricDefinitions
variable {X : Type*} [MetricSpace X]
theorem isOpen_iff_isOpenWrt (S : Set X) : IsOpen S ↔ MetricNotions.IsOpenWrt dist S := by
  rw [Metric.isOpen_iff]
  refine forall₂_congr fun x _ => ?_
  constructor
  · rintro ⟨ε, hε, hball⟩
    exact ⟨ε, hε, fun y hy => hball (Metric.mem_ball'.2 hy)⟩
  · rintro ⟨ε, hε, hball⟩
    exact ⟨ε, hε, fun y hy => hball y (Metric.mem_ball'.1 hy)⟩
theorem closure_eq_closureWrt (S : Set X) : closure S = MetricNotions.closureWrt dist S := by
  ext x
  rw [Metric.mem_closure_iff]
  rfl
theorem isCompact_iff_isCompactWrt (S : Set X) :
    IsCompact S ↔ MetricNotions.IsCompactWrt dist S := by
  constructor
  · intro hS 𝒱 hopen hcover
    obtain ⟨𝒱', hsub, hfin, hcov⟩ := hS.elim_finite_subcover_image (b := 𝒱) (c := id)
      (fun V hV => (isOpen_iff_isOpenWrt V).2 (hopen V hV))
      (by simpa [Set.sUnion_eq_biUnion] using hcover)
    exact ⟨𝒱', hsub, hfin, by simpa [Set.sUnion_eq_biUnion] using hcov⟩
  · intro hS
    refine isCompact_of_finite_subcover fun {ι} V hV hcover => ?_
    obtain ⟨𝒱', hsub, hfin, hcov⟩ := hS (Set.range V)
      (by
        rintro _ ⟨i, rfl⟩
        exact (isOpen_iff_isOpenWrt _).1 (hV i))
      (by rwa [Set.sUnion_range])
    classical
    have hchoose : ∀ W ∈ 𝒱', ∃ i, V i = W := fun W hW => hsub hW
    choose g hg using hchoose
    refine ⟨hfin.toFinset.attach.image fun W => g W.1 (hfin.mem_toFinset.1 W.2), fun x hx => ?_⟩
    obtain ⟨W, hW, hxW⟩ := hcov hx
    refine Set.mem_iUnion₂.2 ⟨g W hW, Finset.mem_image.2
      ⟨⟨W, hfin.mem_toFinset.2 hW⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    rw [hg W hW]
    exact hxW
end MetricDefinitions
variable (s : Conventions.StandingParameters) (E : Ambient)
def PositivelySeparated (A B : Set (Pt s E)) : Prop := setDist s E A B ≠ 0
variable {s E}
def IsC1Fn (f : Pt s E → ℝ) : Prop := ContDiff ℝ 1 (f ∘ proj s E)
theorem isC1Fn_euclidean_iff (f : Pt s .euclidean → ℝ) :
    IsC1Fn f ↔ ContDiff ℝ 1 (fun x : Fin 4 → ℝ => f x) := Iff.rfl
theorem isC1Fn_torus_iff (D : ConnectedFunctions.CouplingData)
    (f : Pt D.toStandingParameters .torus → ℝ) :
    IsC1Fn f ↔ D.IsC1 f := Iff.rfl
def c1CompactlySupportedIn (A : Set (Pt s E)) : Set (Pt s E → ℝ) :=
  {f | IsC1Fn f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ A}
def separatedTuples (s : Conventions.StandingParameters) (E : Ambient) (n : ℕ) :
    Set (Fin n → Pt s E → ℝ) :=
  {f | (∀ i, IsC1Fn (f i) ∧ IsCompact (tsupport (f i))) ∧
    Pairwise fun i j => Disjoint (tsupport (f i)) (tsupport (f j))}
theorem separatedTuples_zero : separatedTuples s E 0 = {fun i => i.elim0} := by
  ext f
  simp only [Set.mem_singleton_iff]
  constructor
  · intro _
    funext i
    exact i.elim0
  · intro _
    exact ⟨fun i => i.elim0, fun i => i.elim0⟩
variable (s E) in
abbrev FunctionTuple : Type := Σ n : ℕ, Fin n → Pt s E → ℝ
def allSeparatedTuples (s : Conventions.StandingParameters) (E : Ambient) :
    Set (FunctionTuple s E) :=
  {T | T.2 ∈ separatedTuples s E T.1}
def nilTuple (s : Conventions.StandingParameters) (E : Ambient) : FunctionTuple s E :=
  ⟨0, fun i => i.elim0⟩
theorem nilTuple_mem_allSeparatedTuples : nilTuple s E ∈ allSeparatedTuples s E := by
  change (fun i : Fin 0 => i.elim0) ∈ separatedTuples s E 0
  rw [separatedTuples_zero]
  rfl
def restrictTuple {X : Type*} {n : ℕ} (f : Fin n → X) (J : Finset (Fin n)) : Fin J.card → X :=
  fun k => f (J.orderEmbOfFin rfl k)
def IsDistIsometry (r : Pt s E ≃ Pt s E) : Prop :=
  ∀ x y, pointDist s E (r x) (r y) = pointDist s E x y
def transportFn {X : Type*} (r : Pt s E ≃ Pt s E) (f : Pt s E → X) : Pt s E → X :=
  f ∘ r.symm
def transportTuple {X : Type*} {n : ℕ} (r : Pt s E ≃ Pt s E) (f : Fin n → Pt s E → X) :
    Fin n → Pt s E → X :=
  fun i => transportFn r (f i)
def permuteTuple {X : Type*} {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : Fin n → X) : Fin n → X :=
  fun i => f (σ i)
end YangMills.Construction.AmbientPoints
