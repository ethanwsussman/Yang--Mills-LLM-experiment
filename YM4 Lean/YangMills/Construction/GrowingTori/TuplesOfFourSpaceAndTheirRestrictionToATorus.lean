import YangMills.Construction.Continuum.FormsOfTheSeparatedTuplesOfFourSpaceTheirSpanAndFunctionals
import YangMills.Construction.GrowingTori.ClassesOfFunctionsTuplesSeparationAndRadius
import YangMills.Construction.GrowingTori.TransportOfAFunctionAndOfATupleToATorus
import YangMills.Construction.GrowingTori.TransportThroughTheBallClassC1OnATorusAndInducedIsometries
import YangMills.Construction.TorusOrFourSpace.ClassesOfFunctionsWithSupportInASet
import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesAdmissibleRadiiAndTheSeparation
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.BallTuples
open TestFunctions (IsLipschitzFor euclidDistR4 setDistR4)
open SourcesAndGluing (ballR4)
abbrev R4Fun : Type := (Fin 4 → ℝ) → ℝ
abbrev FnTuple (q : ℕ) : Type := Fin q → R4Fun
abbrev fnSupport (f : R4Fun) : Set (Fin 4 → ℝ) :=
  SourcesAndGluing.GluingSetup.suppR4 f
section Settings
variable (D : PeriodicSpace.Params) (s : Conventions.StandingParameters)
theorem closure_pt_euclidean (Z : Set (Fin 4 → ℝ)) :
    closure (X := AmbientPoints.Pt s .euclidean) Z = closure Z := by apply _root_.YangMills.Construction.R4TupleForms.closure_pt_euclidean <;> assumption
theorem isCompact_pt_euclidean_iff (Z : Set (Fin 4 → ℝ)) :
    IsCompact (X := AmbientPoints.Pt s .euclidean) Z ↔ IsCompact Z := by apply _root_.YangMills.Construction.R4TupleForms.isCompact_pt_euclidean_iff <;> assumption
theorem supportQ_euclidean (f : R4Fun) :
    PeriodicSpace.Kind.supportQ D .euclidean f = fnSupport f :=
  SeparatedTuplesR4.closureWrt_euclid_eq_closure
    (BallPeriodization.quotDist_euclidean D) _
theorem isCompactQ_euclidean_iff (Z : Set (Fin 4 → ℝ)) :
    PeriodicSpace.Kind.IsCompactQ D .euclidean Z ↔ IsCompact Z :=
  SeparatedTuplesR4.isCompactWrt_euclid_iff (BallPeriodization.quotDist_euclidean D) Z
theorem ambient_topology_euclidean (L : ℕ) :
    (GrowingTori.Ambient.euclidean : GrowingTori.Ambient L).topology =
      (inferInstance : TopologicalSpace (Fin 4 → ℝ)) :=
  TopologicalSpace.ext_iff.2 fun U =>
    SeparatedTuplesR4.isOpenWrt_euclid_iff (fun _ _ => rfl) U
theorem ambient_supp_euclidean (L : ℕ) (f : R4Fun) :
    (GrowingTori.Ambient.euclidean : GrowingTori.Ambient L).supp f = fnSupport f := by
  change @closure _ (GrowingTori.Ambient.euclidean : GrowingTori.Ambient L).topology _ = _
  rw [ambient_topology_euclidean]
  rfl
end Settings
def IsSepLipschitz {q : ℕ} (X : FnTuple q) : Prop :=
  (∀ l, IsLipschitzFor euclidDistR4 (X l)) ∧ (∀ l, IsCompact (fnSupport (X l))) ∧
    ∀ l l', l ≠ l' → Disjoint (fnSupport (X l)) (fnSupport (X l'))
theorem isSepLipschitz_zero (X : FnTuple 0) :
    IsSepLipschitz X ∧ X = fun l => l.elim0 :=
  ⟨⟨fun l => l.elim0, fun l => l.elim0, fun l => l.elim0⟩, funext fun l => l.elim0⟩
def AllSupportedIn {q : ℕ} (X : FnTuple q) (A : Set (Fin 4 → ℝ)) : Prop :=
  ∀ l, SourcesAndGluing.HasCompactSupportIn (X l) A
section Sets
variable (D : PeriodicSpace.Params)
def cutoffOneParams : Conventions.StandingParameters := ⟨D.L, D.isAdmissible, 1, D.m⟩
def sepTuples (E : ReflectionPositivity.AxisMirror.Ambient) (q : ℕ) :
    Set (Fin q → AmbientPoints.Pt (cutoffOneParams D) E → ℝ) :=
  AmbientPoints.separatedTuples (cutoffOneParams D) E q
def sepTuplesR4 (q : ℕ) : Set (FnTuple q) :=
  sepTuples D .euclidean q
def sepTuplesBall (q : ℕ) (ρ : ℝ) : Set (FnTuple q) :=
  {X | X ∈ sepTuplesR4 D q ∧ AllSupportedIn X (ballR4 ρ)}
abbrev subTupleOn {q : ℕ} (X : FnTuple q) (J : Finset (Fin q)) : FnTuple J.card :=
  AmbientPoints.restrictTuple X J
theorem tsupport_pt_euclidean (s : Conventions.StandingParameters)
    (f : AmbientPoints.Pt s .euclidean → ℝ) :
    tsupport f = fnSupport f :=
  closure_pt_euclidean s (Function.support f)
variable {D}
theorem mem_sepTuplesR4_iff {q : ℕ} (X : FnTuple q) :
    X ∈ sepTuplesR4 D q ↔
      (∀ l, ContDiff ℝ 1 (X l)) ∧ (∀ l, IsCompact (fnSupport (X l))) ∧
        ∀ l l', l ≠ l' → Disjoint (fnSupport (X l)) (fnSupport (X l')) := by
  have hc : ∀ l, IsCompact (X := AmbientPoints.Pt (cutoffOneParams D) .euclidean)
      (tsupport (X := AmbientPoints.Pt (cutoffOneParams D) .euclidean) (X l)) ↔
        IsCompact (fnSupport (X l)) := fun l =>
    (Iff.of_eq (congrArg (IsCompact (X := AmbientPoints.Pt (cutoffOneParams D) .euclidean))
      (tsupport_pt_euclidean (cutoffOneParams D) (X l)))).trans (isCompact_pt_euclidean_iff _ _)
  have hd : ∀ l l', Disjoint (tsupport (X := AmbientPoints.Pt (cutoffOneParams D) .euclidean) (X l))
      (tsupport (X := AmbientPoints.Pt (cutoffOneParams D) .euclidean) (X l')) =
        Disjoint (fnSupport (X l)) (fnSupport (X l')) := fun l l' =>
    congrArg₂ Disjoint (tsupport_pt_euclidean (cutoffOneParams D) (X l))
      (tsupport_pt_euclidean (cutoffOneParams D) (X l'))
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun l => (h₁ l).1, fun l => (hc l).1 (h₁ l).2, fun l l' hl =>
      Eq.mp (hd l l') (h₂ hl)⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨fun l => ⟨h₁ l, (hc l).2 (h₂ l)⟩, fun l l' hl => Eq.mpr (hd l l') (h₃ l l' hl)⟩
theorem mem_sepC1Tuples_euclidean_iff {q : ℕ} (X : FnTuple q) :
    X ∈ PeriodicSpace.Kind.sepC1Tuples D .euclidean q ↔
      (∀ l, ContDiff ℝ 1 (X l)) ∧ (∀ l, IsCompact (fnSupport (X l))) ∧
        ∀ l l', l ≠ l' → Disjoint (fnSupport (X l)) (fnSupport (X l')) := by
  have hc : ∀ l, PeriodicSpace.Kind.IsCompactQ D .euclidean
      (PeriodicSpace.Kind.supportQ D .euclidean (X l)) ↔ IsCompact (fnSupport (X l)) :=
    fun l => by
      rw [supportQ_euclidean]
      exact isCompactQ_euclidean_iff D _
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨h₁, fun l => (hc l).1 (h₂ l), fun l l' hl => ?_⟩
    have h := h₃ l l' hl
    rw [supportQ_euclidean, supportQ_euclidean] at h
    exact h
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨h₁, fun l => (hc l).2 (h₂ l), fun l l' hl => ?_⟩
    rw [supportQ_euclidean, supportQ_euclidean]
    exact h₃ l l' hl
variable (D)
theorem ballR4_eq_centredBall {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ballR4 ρ =
      PeriodicSpace.Kind.centredBall D .euclidean (ENNReal.ofReal ρ) := by
  ext x
  rw [PeriodicSpace.Kind.centredBall, if_neg ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hρ]
  change TorusMetric.euclidNormVec x < ρ ↔
    PeriodicSpace.Kind.quotDist D .euclidean x (0 : Fin 4 → ℝ) < ρ
  rw [BallPeriodization.quotDist_euclidean, sub_zero]
end Sets
theorem isLipschitzFor_of_contDiff {f : R4Fun} (h : ContDiff ℝ 1 f)
    (hc : IsCompact (fnSupport f)) : IsLipschitzFor euclidDistR4 f := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) (f := f) hc h one_ne_zero
  refine ⟨C, C.2, fun x y => ?_⟩
  calc ‖f x - f y‖ = dist (f x) (f y) := (dist_eq_norm _ _).symm
    _ ≤ C * dist x y := hC.dist_le_mul x y
    _ ≤ C * euclidDistR4 x y := by
      refine mul_le_mul_of_nonneg_left ?_ C.2
      rw [dist_eq_norm]
      exact SeparatedTuplesR4.norm_le_euclidNormVec _
theorem isSepLipschitz_of_mem_sepTuplesR4 {D : PeriodicSpace.Params} {q : ℕ} {X : FnTuple q}
    (hX : X ∈ sepTuplesR4 D q) : IsSepLipschitz X := by
  obtain ⟨h₁, h₂, h₃⟩ := (mem_sepTuplesR4_iff X).1 hX
  exact ⟨fun l => isLipschitzFor_of_contDiff (h₁ l) (h₂ l), h₂, h₃⟩
def minSupportDist {q : ℕ} (X : FnTuple q) : ℝ≥0∞ :=
  ⨅ l, ⨅ l', ⨅ _ : l ≠ l', setDistR4 (fnSupport (X l)) (fnSupport (X l'))
section Admissible
variable (L : ℕ) {V : Type*} [Zero V] {q : ℕ}
abbrev IsBallSupported (R : ℝ) (X : Fin q → (Fin 4 → ℝ) → V) : Prop :=
  (GrowingTori.Ambient.euclidean : GrowingTori.Ambient L).IsRSupported R X
end Admissible
section Functionals
variable (D : PeriodicSpace.Params)
def lipClass (A : Set (Fin 4 → ℝ)) : Set R4Fun :=
  PeriodicSpace.Kind.lipschitzSupportedIn D .euclidean A
variable {D}
variable (D)
def lipTuplesBall (q : ℕ) (ρ : ℝ) : Set (FnTuple q) :=
  {X | IsSepLipschitz X ∧ AllSupportedIn X (ballR4 ρ)}
theorem permuteTuple_mem_lipTuplesBall {q : ℕ} {ρ : ℝ} {X : FnTuple q}
    (hX : X ∈ lipTuplesBall q ρ) (σ : Equiv.Perm (Fin q)) :
    AmbientPoints.permuteTuple σ X ∈ lipTuplesBall q ρ :=
  ⟨⟨fun l => hX.1.1 (σ l), fun l => hX.1.2.1 (σ l),
      fun l l' hl => hX.1.2.2 (σ l) (σ l') (σ.injective.ne hl)⟩, fun l => hX.2 (σ l)⟩
variable {D}
def IsMultilinearOn {q : ℕ} (K : Set (FnTuple q)) (V : Fin q → Set R4Fun)
    (Ψ : K → ℝ) : Prop :=
  ∀ X : FnTuple q, (∀ l, X l ∈ V l) → ∀ (l : Fin q) (f g : R4Fun) (a b : ℝ),
    f ∈ V l → g ∈ V l →
    ∀ (hf : Function.update X l f ∈ K) (hg : Function.update X l g ∈ K)
      (hc : Function.update X l (a • f + b • g) ∈ K),
      Ψ ⟨_, hc⟩ = a * Ψ ⟨_, hf⟩ + b * Ψ ⟨_, hg⟩
variable (D)
def IsLipDisjointMultilinear {q : ℕ} {ρ : ℝ}
    (Ψ : lipTuplesBall q ρ → ℝ) : Prop :=
  ∀ A : Fin q → Set (Fin 4 → ℝ), (∀ l, A l ⊆ ballR4 ρ) →
    (∀ l l', l ≠ l' → Disjoint (A l) (A l')) →
    IsMultilinearOn (lipTuplesBall q ρ) (fun l => lipClass D (A l)) Ψ
def IsLipPermInvariant {q : ℕ} {ρ : ℝ} (Ψ : lipTuplesBall q ρ → ℝ) : Prop :=
  ∀ (X : lipTuplesBall q ρ) (σ : Equiv.Perm (Fin q)),
    Ψ ⟨_, permuteTuple_mem_lipTuplesBall X.2 σ⟩ = Ψ X
end Functionals
section Transport
variable (D : PeriodicSpace.Params)
def IsPeriodizable (ρ : ℝ) {n : ℕ} (X : FnTuple n) : Prop :=
  0 < ρ ∧ ρ ≤ BallPeriodization.ballRadius D ∧ IsSepLipschitz X ∧
    AllSupportedIn X (ballR4 ρ)
def periodize {n : ℕ} (X : FnTuple n) : Fin n → D.Torus → ℝ :=
  GrowingTori.Ambient.periodizeTuple (BallPeriodization.side_mem_torusSides D) X
theorem periodize_apply {n : ℕ} (X : FnTuple n) (l : Fin n) :
    periodize D X l = TestFunctions.periodize D.side (X l) :=
  rfl
def connectedFn (K : ℕ+) (β : ℝ) {n : ℕ} (X : FnTuple n) : ℂ :=
  SchwingerFunctions.connectedSchwingerR4 D.L D.m K β X
theorem connectedFn_eq_connectedSchwinger (K : ℕ+) (β : ℝ) {n : ℕ} (X : FnTuple n) :
    connectedFn D K β X = SchwingerFunctions.connectedSchwinger D.L D.m K β (periodize D X) :=
  rfl
variable {D}
theorem IsPeriodizable.apply {ρ : ℝ} {n : ℕ} {X : FnTuple n}
    (h : IsPeriodizable D ρ X) (l : Fin n) :
    BallPeriodization.IsPeriodizableInBall D ρ (X l) :=
  ⟨h.1, h.2.1, h.2.2.2 l⟩
end Transport
end YangMills.Construction.BallTuples
end
