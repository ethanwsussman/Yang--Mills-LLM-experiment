import YangMills.Construction.Torus.FunctionsOfSeveralPointsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TestFunctions YangMills.Construction.TorusMetric
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints
variable {s : Conventions.StandingParameters} {E : Ambient} {n : ℕ}
def asFunctionOnOnePoint (f : Pt s E → ℝ) : Tuple s E 1 → ℂ := fun y => (f (y 0) : ℂ)
def IsC1 (f : Pt s E → ℝ) : Prop := IsCn 1 (asFunctionOnOnePoint f)
theorem closedSupport_asFunctionOnOnePoint (f : Pt s E → ℝ) :
    closedSupport (asFunctionOnOnePoint f) = (fun y : Tuple s E 1 => y 0) ⁻¹' tsupport f := by
  have h := (Homeomorph.funUnique (Fin 1) (Pt s E)).preimage_closure (Function.support f)
  have h2 : {y : Tuple s E 1 | asFunctionOnOnePoint f y ≠ 0} =
      (Homeomorph.funUnique (Fin 1) (Pt s E)) ⁻¹' Function.support f := by
    ext y
    simp [asFunctionOnOnePoint]
  rw [closedSupport, h2, ← h]
  rfl
def c1CompactSupportIn (A : Set (Pt s E)) : Set (Pt s E → ℝ) :=
  {f | IsC1 f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ A}
def CompactDisjointSupports (f : Fin n → Pt s E → ℝ) : Prop :=
  (∀ i, IsCompact (tsupport (f i))) ∧
    ∀ i i', i ≠ i' → Disjoint (tsupport (f i)) (tsupport (f i'))
def SupportsWithin (f : Fin n → Pt s E → ℝ) (O : Set (Pt s E)) : Prop :=
  ∀ i, tsupport (f i) ⊆ O
variable (s E n) in
def sepTuples : Set (Fin n → Pt s E → ℝ) :=
  {f | (∀ i, IsC1 (f i)) ∧ CompactDisjointSupports f}
variable (s E n) in
def sepLipTuples : Set (Fin n → Pt s E → ℝ) :=
  {f | (∀ i, IsLipschitzFor (pointDist s E) (f i)) ∧ CompactDisjointSupports f}
variable (n) in
def sepTuplesIn (O : Set (Pt s E)) : Set (Fin n → Pt s E → ℝ) :=
  {f | f ∈ sepTuples s E n ∧ SupportsWithin f O}
variable (n) in
def sepLipTuplesIn (O : Set (Pt s E)) : Set (Fin n → Pt s E → ℝ) :=
  {f | f ∈ sepLipTuples s E n ∧ SupportsWithin f O}
theorem sepTuplesIn_univ :
    sepTuplesIn n (univ : Set (Pt s E)) = sepTuples s E n := by
  ext f
  simp [sepTuplesIn, SupportsWithin]
def supportGap (f : Fin n → Pt s E → ℝ) : ℝ≥0∞ :=
  ⨅ i, ⨅ i', ⨅ _ : i ≠ i', setDist s E (tsupport (f i)) (tsupport (f i'))
theorem isLeast_supportGap (hn : 2 ≤ n) (f : Fin n → Pt s E → ℝ) :
    IsLeast ((fun p : Fin n × Fin n => setDist s E (tsupport (f p.1)) (tsupport (f p.2))) ''
      {p | p.1 ≠ p.2}) (supportGap f) := by
  have hne : ({p | p.1 ≠ p.2} : Set (Fin n × Fin n)).Nonempty :=
    ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.ext_iff]⟩
  obtain ⟨p, hp, hmin⟩ := Set.exists_min_image _
    (fun p : Fin n × Fin n => setDist s E (tsupport (f p.1)) (tsupport (f p.2)))
    (Set.toFinite _) hne
  have heq : supportGap f = setDist s E (tsupport (f p.1)) (tsupport (f p.2)) := by
    apply le_antisymm
    · exact iInf_le_of_le p.1 (iInf_le_of_le p.2 (iInf_le_of_le hp le_rfl))
    · exact le_iInf fun i => le_iInf fun i' => le_iInf fun h => hmin (i, i') h
  refine ⟨⟨p, hp, heq.symm⟩, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  rw [heq]
  exact hmin q hq
def SupportsApartBy (f : Fin n → Pt s E → ℝ) (d : ℝ) : Prop :=
  0 < d ∧ ENNReal.ofReal d ≤ supportGap f
def SupportsInBalls (R : ℝ) (f : Fin n → Pt s E → ℝ) : Prop :=
  ∀ i, ∃ y, tsupport (f i) ⊆ closedBall s E y R
theorem dist_toLp_eq_euclidNormVec (x y : Fin 4 → ℝ) :
    dist (WithLp.toLp 2 x : PiLp 2 fun _ : Fin 4 => ℝ) (WithLp.toLp 2 y) = euclidNormVec (x - y) := by
  rw [dist_eq_norm, ← WithLp.toLp_sub, euclidNormVec_eq_norm]
theorem dist_toLp_eq_torusEuclidNorm {S : ℝ} (x y : Torus4 S) :
    dist (WithLp.toLp 2 x : PiLp 2 fun _ : Fin 4 => AddCircle S) (WithLp.toLp 2 y) =
      torusEuclidNorm (x - y) := by
  rw [dist_eq_norm, ← WithLp.toLp_sub, torusEuclidNorm_eq_norm]
def homeomorphR4 (s : Conventions.StandingParameters) : Pt s .euclidean ≃ₜ (Fin 4 → ℝ) :=
  have hg : Isometry (fun x : Pt s .euclidean =>
      (WithLp.toLp 2 (x : Fin 4 → ℝ) : PiLp 2 fun _ : Fin 4 => ℝ)) :=
    Isometry.of_dist_eq fun x y => dist_toLp_eq_euclidNormVec x y
  { toEquiv := Equiv.refl _
    continuous_toFun := (PiLp.continuous_ofLp 2 _).comp hg.continuous
    continuous_invFun := hg.isEmbedding.continuous_iff.mpr (PiLp.continuous_toLp 2 _) }
def homeomorphTorus (s : Conventions.StandingParameters) :
    Pt s .torus ≃ₜ Torus4 (PeriodicLattice.torusSide s.L s.m) :=
  have hg : Isometry (fun x : Pt s .torus =>
      (WithLp.toLp 2 (x : Torus4 (PeriodicLattice.torusSide s.L s.m)) :
        PiLp 2 fun _ : Fin 4 => AddCircle (PeriodicLattice.torusSide s.L s.m))) :=
    Isometry.of_dist_eq fun x y => dist_toLp_eq_torusEuclidNorm x y
  { toEquiv := Equiv.refl _
    continuous_toFun := (PiLp.continuous_ofLp 2 _).comp hg.continuous
    continuous_invFun := hg.isEmbedding.continuous_iff.mpr (PiLp.continuous_toLp 2 _) }
theorem tsupport_eq_of_r4 (f : Pt s .euclidean → ℝ) :
    tsupport f = tsupport (X := Fin 4 → ℝ) f := by
  have hid : ∀ A : Set (Pt s .euclidean), (homeomorphR4 s) '' A = A := fun A => by
    ext x
    exact ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ⟨x, hx, rfl⟩⟩
  exact (hid _).symm.trans (((homeomorphR4 s).image_closure (Function.support f)).trans
    (congrArg (closure (X := Fin 4 → ℝ)) (hid _)))
theorem tsupport_eq_of_torus (f : Pt s .torus → ℝ) :
    tsupport f = tsupport (X := Torus4 (PeriodicLattice.torusSide s.L s.m)) f := by
  have hid : ∀ A : Set (Pt s .torus), (homeomorphTorus s) '' A = A := fun A => by
    ext x
    exact ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ⟨x, hx, rfl⟩⟩
  exact (hid _).symm.trans (((homeomorphTorus s).image_closure (Function.support f)).trans
    (congrArg (closure (X := Torus4 (PeriodicLattice.torusSide s.L s.m))) (hid _)))
theorem supportsApartBy_torus_iff (f : Fin n → Pt s .torus → ℝ) (d : ℝ) :
    SupportsApartBy f d ↔
      HasSeparatedSupportsTorus (ℓ := PeriodicLattice.torusSide s.L s.m) (E := ℝ) f d := by
  simp only [SupportsApartBy, HasSeparatedSupportsTorus, supportGap, le_iInf_iff,
    tsupport_eq_of_torus]
  rfl
abbrev TupleForm (𝔖 : Set (Fin n → Pt s E → ℝ)) : Type := 𝔖 → ℂ
def TupleForm.IsReal {𝔖 : Set (Fin n → Pt s E → ℝ)} (Φ : TupleForm 𝔖) : Prop := ∀ f, (Φ f).im = 0
def TupleForm.IsMultilinear {𝔖 : Set (Fin n → Pt s E → ℝ)} (Φ : TupleForm 𝔖) : Prop :=
  ∀ (l : Fin n) (b b' : ℝ) (f f' : 𝔖),
    (∀ i, i ≠ l → (f : Fin n → Pt s E → ℝ) i = (f' : Fin n → Pt s E → ℝ) i) →
    ∀ h : Function.update (f : Fin n → Pt s E → ℝ) l
        (b • (f : Fin n → Pt s E → ℝ) l + b' • (f' : Fin n → Pt s E → ℝ) l) ∈ 𝔖,
      Φ ⟨_, h⟩ = (b : ℂ) * Φ f + (b' : ℂ) * Φ f'
variable (s E n) in
def pairwiseDistinctTuples : Set (Tuple s E n) := injectiveTuples (Pt s E) n
end YangMills.Construction.AmbientPoints
