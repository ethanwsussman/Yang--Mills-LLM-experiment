import YangMills.Construction.InfiniteLattice.TuplesCombinationsNormalsAndMirrorsOfFourSpace
import YangMills.Construction.ReflectionPositivity.ReflectionsHyperplanesMirrorsAndOpenSides
import YangMills.Construction.Torus.CoordinateReflectionsMirrorsAndSlabs
import YangMills.Construction.Torus.HypercubicGroupTranslationsAndInvarianceOnTorusOrFourSpace
import YangMills.Construction.Torus.LipschitzTuplesSeparationConcatenationAndTransport
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AmbientPoints
open YangMills.Construction.ReflectionPositivity.AxisMirror
open YangMills.Construction.LatticeConventions (euclidDot basisVector)
open YangMills.Construction.TorusMetric
open YangMills.Construction.InfiniteLattice.EuclideanMirrors
def AmbientMirror : Ambient → Type
  | .torus => CoordMirror
  | .euclidean => AffineMirror
namespace AmbientMirror
def ofAxisLevel : (E : Ambient) → Fin 4 → ℝ → AmbientMirror E
  | .torus, μ, c => (⟨μ, c⟩ : CoordMirror)
  | .euclidean, μ, c => (⟨⟨basisVector μ, Or.inl ⟨μ, rfl⟩⟩, c⟩ : AffineMirror)
def IsAxial : (E : Ambient) → AmbientMirror E → Prop
  | .torus, _ => True
  | .euclidean, M => AffineMirror.IsAxial M
theorem sqNorm_basisVector (κ : Fin 4) (h : basisVector κ ∈ reflectionNormals) :
    ReflNormal.sqNorm ⟨basisVector κ, h⟩ = 1 := by
  rw [ReflNormal.sqNorm_eq_euclidDot]
  fin_cases κ <;> simp [euclidDot, basisVector, Fin.sum_univ_four]
theorem sqNorm_of_diagonal {n : Fin 4 → ℝ} (h : n ∈ reflectionNormals) {κ lam : Fin 4}
    (hlt : κ < lam) (hn : n = basisVector κ + basisVector lam ∨ n = basisVector κ - basisVector lam) :
    ReflNormal.sqNorm ⟨n, h⟩ = 2 := by
  rw [ReflNormal.sqNorm_eq_euclidDot]
  rcases hn with rfl | rfl <;> fin_cases κ <;> fin_cases lam <;> first
    | exact absurd hlt (by decide)
    | (simp [euclidDot, basisVector, Fin.sum_univ_four]; try norm_num)
theorem isAxial_euclidean_iff (M : AffineMirror) :
    IsAxial .euclidean M ↔ ∃ μ, M.normal.1 = basisVector μ := by
  obtain ⟨⟨n, hn⟩, c⟩ := M
  constructor
  · intro h
    rcases hn with ⟨κ, rfl⟩ | ⟨κ, lam, hlt, hd⟩
    · exact ⟨κ, rfl⟩
    · have h2 := sqNorm_of_diagonal (Or.inr ⟨κ, lam, hlt, hd⟩) hlt hd
      have h1 : ReflNormal.sqNorm ⟨n, _⟩ = 1 := h
      rw [h2] at h1
      norm_num at h1
  · rintro ⟨μ, hμ⟩
    have hμ' : n = basisVector μ := hμ
    subst hμ'
    exact sqNorm_basisVector μ _
variable (s : Conventions.StandingParameters)
def positiveSide : (E : Ambient) → AmbientMirror E → Set (Pt s E)
  | .torus, M => AxisReflection.upperHalf (PeriodicLattice.torusSide s.L s.m)
      (CoordMirror.axis M) (CoordMirror.height M)
  | .euclidean, M => AffineMirror.positiveSide M
def reflect : (E : Ambient) → AmbientMirror E → (Pt s E ≃ Pt s E)
  | .torus, M => AxisReflection.torusCoordReflect (PeriodicLattice.torusSide s.L s.m)
      (CoordMirror.axis M) (CoordMirror.height M)
  | .euclidean, M => hyperplaneReflectionEquiv s (AffineMirror.normal M)
      (AffineMirror.offset M)
def liftReflect : (E : Ambient) → AmbientMirror E → (Fin 4 → ℝ) → Fin 4 → ℝ
  | .torus, M => AxisReflection.coordReflect (CoordMirror.axis M)
      (CoordMirror.height M)
  | .euclidean, M => hyperplaneReflection (AffineMirror.normal M)
      (AffineMirror.offset M)
theorem reflect_euclidean_apply (M : AffineMirror) (x : Fin 4 → ℝ) :
    (reflect s .euclidean M x : Fin 4 → ℝ) =
      x - (2 * (euclidDot M.normal.1 x - M.offset) / euclidNormVec M.normal.1 ^ 2) • M.normal.1 := by
  change x - (2 * (euclidDot M.normal.1 x - M.offset)) • M.normal.dual = _
  simp only [ReflNormal.dual, ReflNormal.sqNorm, smul_smul, div_eq_mul_inv]
theorem reflect_proj (E : Ambient) (M : AmbientMirror E) (y : Fin 4 → ℝ) :
    reflect s E M (proj s E y) = proj s E (liftReflect E M y) := by
  cases E with
  | torus => exact AxisReflection.torusCoordReflect_torusProj _ _ _ _
  | euclidean => rfl
theorem contDiff_liftReflect (E : Ambient) (M : AmbientMirror E) :
    ContDiff ℝ 1 (liftReflect E M) := by
  cases E with
  | torus =>
    change ContDiff ℝ 1 fun x : Fin 4 → ℝ => x + (2 * (_ - x _)) • (Pi.single _ 1 : Fin 4 → ℝ)
    fun_prop
  | euclidean =>
    change ContDiff ℝ 1 fun x : Fin 4 → ℝ => x - (2 * (∑ μ, _ * x μ - _)) • _
    fun_prop
theorem reflect_reflect (E : Ambient) (M : AmbientMirror E) (x : Pt s E) :
    reflect s E M (reflect s E M x) = x := by
  cases E with
  | torus =>
    obtain ⟨y, rfl⟩ := TestFunctions.torusProj_surjective (PeriodicLattice.torusSide s.L s.m) x
    change AxisReflection.torusCoordReflect _ _ _ (AxisReflection.torusCoordReflect _ _ _ _) = _
    rw [AxisReflection.torusCoordReflect_torusProj, AxisReflection.torusCoordReflect_torusProj,
      AxisReflection.coordReflect_involutive]
  | euclidean => exact hyperplaneReflection_hyperplaneReflection _ _ _
theorem reflect_symm (E : Ambient) (M : AmbientMirror E) :
    (reflect s E M).symm = reflect s E M :=
  Equiv.ext fun x => by rw [Equiv.symm_apply_eq, reflect_reflect]
theorem torusEuclidNorm_torusCoordReflect_sub (ℓ : ℝ) (μ : Fin 4) (c : ℝ) (x y : Torus4 ℓ) :
    torusEuclidNorm (AxisReflection.torusCoordReflect ℓ μ c x -
      AxisReflection.torusCoordReflect ℓ μ c y) = torusEuclidNorm (x - y) := by
  obtain ⟨a, rfl⟩ := TestFunctions.torusProj_surjective ℓ x
  obtain ⟨b, rfl⟩ := TestFunctions.torusProj_surjective ℓ y
  rw [AxisReflection.torusCoordReflect_torusProj, AxisReflection.torusCoordReflect_torusProj,
    torusEuclidNorm_eq_sqrt, torusEuclidNorm_eq_sqrt]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  by_cases h : ν = μ
  · subst h
    simp only [torusProj, Pi.sub_apply, AxisReflection.coordReflect_apply_same]
    rw [← AddCircle.coe_sub, ← AddCircle.coe_sub,
      show 2 * c - a ν - (2 * c - b ν) = -(a ν - b ν) by ring, AddCircle.coe_neg, norm_neg]
  · simp only [torusProj, Pi.sub_apply, AxisReflection.coordReflect_apply_ne h]
theorem isDistIsometry_reflect (E : Ambient) (M : AmbientMirror E) : IsDistIsometry (reflect s E M) := by
  cases E with
  | euclidean => exact isDistIsometry_hyperplaneReflectionEquiv s _ _
  | torus => exact torusEuclidNorm_torusCoordReflect_sub _ _ _
def reflectHomeomorph (E : Ambient) (M : AmbientMirror E) : Pt s E ≃ₜ Pt s E :=
  (IsometryEquiv.mk (reflect s E M)
    (Isometry.of_dist_eq (isDistIsometry_reflect s E M))).toHomeomorph
theorem disjoint_preimage_upperHalf {ℓ : ℝ} (hℓ : 0 < ℓ) (μ : Fin 4) (c : ℝ) :
    Disjoint (AxisReflection.torusCoordReflect ℓ μ c ⁻¹' AxisReflection.upperHalf ℓ μ c)
      (AxisReflection.upperHalf ℓ μ c) := by
  refine Set.disjoint_left.2 ?_
  rintro x ⟨y', ⟨h1', h2'⟩, hθ⟩ ⟨y, ⟨h1, h2⟩, rfl⟩
  rw [AxisReflection.torusCoordReflect_torusProj] at hθ
  have hμ : ((y' μ : ℝ) : AddCircle ℓ) = ((2 * c - y μ : ℝ) : AddCircle ℓ) := by
    have := congrFun hθ μ
    simpa only [torusProj, AxisReflection.coordReflect_apply_same] using this
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 hμ)
  have hk' : (k : ℝ) * ℓ = -y' μ + (2 * c - y μ) := by simpa using hk
  have hneg : (k : ℝ) * ℓ < 0 := by rw [hk']; linarith
  have hgt : -ℓ < (k : ℝ) * ℓ := by rw [hk']; linarith
  have hk0 : k < 0 := by
    by_contra hc
    have : (0 : ℝ) ≤ k := by exact_mod_cast not_lt.1 hc
    nlinarith
  have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
  nlinarith
theorem not_both_positive (M : AffineMirror) (x : Fin 4 → ℝ)
    (h1 : M.offset < euclidDot M.normal.1 (hyperplaneReflection M.normal M.offset x))
    (h2 : M.offset < euclidDot M.normal.1 x) : False := by
  rw [euclidDot_hyperplaneReflection] at h1
  linarith
theorem disjoint_preimage_positiveSide (E : Ambient) (M : AmbientMirror E) :
    Disjoint (reflect s E M ⁻¹' positiveSide s E M) (positiveSide s E M) := by
  cases E with
  | torus =>
    refine disjoint_preimage_upperHalf ?_ _ _
    have hL : 0 < s.L := by
      have := s.isAdmissible.2
      omega
    unfold PeriodicLattice.torusSide
    positivity
  | euclidean =>
    exact Set.disjoint_left.2 fun x hx hy => not_both_positive M x hx hy
theorem coordReflect_eq_euclidReflect (μ : Fin 4) (c : ℝ) :
    AxisReflection.coordReflect μ c = euclidReflect μ c := by
  funext y ν
  by_cases h : ν = μ
  · subst h
    rw [AxisReflection.coordReflect_apply_same]
    simp [euclidReflect, PeriodicLattice.coordVec]
    ring
  · rw [AxisReflection.coordReflect_apply_ne h]
    simp [euclidReflect, PeriodicLattice.coordVec, h]
theorem euclidDot_basisVector (μ : Fin 4) (x : Fin 4 → ℝ) : euclidDot (basisVector μ) x = x μ := by
  simp [euclidDot, basisVector, Pi.single_apply]
theorem positiveSide_torus (D : MirrorData) (M : CoordMirror) :
    positiveSide D.toStandingParameters .torus M = M.upperSide D .torus := by
  change AxisReflection.upperHalf _ _ _ = D.projection '' _
  refine congrArg (D.projection '' ·) ?_
  ext y
  change (M.height < y M.axis ∧ y M.axis < M.height + D.side / 2) ↔
    (0 < y M.axis - M.height ∧ y M.axis - M.height < D.side / 2)
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
theorem reflect_torus (D : MirrorData) (M : CoordMirror) :
    (reflect D.toStandingParameters .torus M : D.Torus → D.Torus) = M.reflect D .torus := by
  have hI : D.Induces (euclidReflect M.axis M.height)
      (AxisReflection.torusCoordReflect (PeriodicLattice.torusSide D.L D.m) M.axis M.height) := by
    funext y
    rw [← coordReflect_eq_euclidReflect]
    exact AxisReflection.torusCoordReflect_torusProj _ _ _ _
  have hE : D.Induces (euclidReflect M.axis M.height)
      (D.descended (euclidReflect M.axis M.height)) :=
    Classical.epsilon_spec (p := D.Induces _) ⟨_, hI⟩
  funext x
  obtain ⟨y, rfl⟩ := TestFunctions.torusProj_surjective (PeriodicLattice.torusSide D.L D.m) x
  exact (congrFun hI y).trans (congrFun hE y).symm
variable {s} in
def separatedIn {E : Ambient} (O : Set (Pt s E)) : Set (FunctionTuple s E) :=
  {X | X ∈ allSeparatedTuples s E ∧ ∀ i, tsupport (X.2 i) ⊆ O}
def reflectTuple (E : Ambient) (M : AmbientMirror E) (X : FunctionTuple s E) : FunctionTuple s E :=
  TorusSymmetries.transportAnyTuple (reflect s E M) X
theorem transportTuple_reflect (E : Ambient) (M : AmbientMirror E) {n : ℕ}
    (f : Fin n → Pt s E → ℝ) (i : Fin n) :
    transportTuple (reflect s E M) f i = f i ∘ reflect s E M := by
  change f i ∘ (reflect s E M).symm = _
  rw [reflect_symm]
theorem tsupport_transportTuple_reflect (E : Ambient) (M : AmbientMirror E) {n : ℕ}
    (f : Fin n → Pt s E → ℝ) (i : Fin n) :
    tsupport (transportTuple (reflect s E M) f i) = reflect s E M ⁻¹' tsupport (f i) := by
  rw [transportTuple_reflect]
  unfold tsupport
  rw [Function.support_comp_eq_preimage]
  exact ((reflectHomeomorph s E M).preimage_closure _).symm
theorem isC1Fn_comp_reflect (E : Ambient) (M : AmbientMirror E) {f : Pt s E → ℝ}
    (hf : IsC1Fn f) : IsC1Fn (f ∘ reflect s E M) := by
  have h : (f ∘ reflect s E M) ∘ proj s E =
      (f ∘ proj s E) ∘ liftReflect E M :=
    funext fun y => congrArg f (reflect_proj s E M y)
  change ContDiff ℝ 1 ((f ∘ reflect s E M) ∘ proj s E)
  rw [h]
  exact ContDiff.comp hf (contDiff_liftReflect E M)
theorem reflectTuple_mem (E : Ambient) (M : AmbientMirror E) {X : FunctionTuple s E}
    (hX : X ∈ allSeparatedTuples s E) :
    reflectTuple s E M X ∈ allSeparatedTuples s E := by
  have hX' : X.2 ∈ separatedTuples s E X.1 := hX
  change transportTuple (reflect s E M) X.2 ∈ separatedTuples s E X.1
  refine ⟨fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
  · rw [transportTuple_reflect]
    exact isC1Fn_comp_reflect s E M (hX'.1 i).1
  · rw [tsupport_transportTuple_reflect]
    exact (reflectHomeomorph s E M).isCompact_preimage.2 (hX'.1 i).2
  · change Disjoint (tsupport _) (tsupport _)
    rw [tsupport_transportTuple_reflect, tsupport_transportTuple_reflect]
    exact (hX'.2 hij).preimage _
variable {s} in
theorem tupleAppend_mem {E : Ambient} {X Y : FunctionTuple s E}
    (hX : X ∈ allSeparatedTuples s E) (hY : Y ∈ allSeparatedTuples s E)
    (h : ∀ i j, Disjoint (tsupport (X.2 i)) (tsupport (Y.2 j))) :
    tupleAppend X Y ∈ allSeparatedTuples s E := by
  have hX' : X.2 ∈ separatedTuples s E X.1 := hX
  have hY' : Y.2 ∈ separatedTuples s E Y.1 := hY
  change Fin.append X.2 Y.2 ∈ separatedTuples s E (X.1 + Y.1)
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simpa using hX'.1 a
    · simpa using hY'.1 b
  · induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left b => simpa using hX'.2 (fun e => hij (by rw [e]) : a ≠ b)
      | right b => simpa using h a b
    | right a =>
      induction j using Fin.addCases with
      | left b => simpa using (h b a).symm
      | right b => simpa using hY'.2 (fun e => hij (by rw [e]) : a ≠ b)
theorem reflectAppend_mem (E : Ambient) (M : AmbientMirror E) {X Y : FunctionTuple s E}
    (hX : X ∈ separatedIn (positiveSide s E M)) (hY : Y ∈ separatedIn (positiveSide s E M)) :
    tupleAppend (reflectTuple s E M X) Y ∈ allSeparatedTuples s E := by
  refine tupleAppend_mem (reflectTuple_mem s E M hX.1) hY.1 fun (i : Fin X.1) j => ?_
  change Disjoint (tsupport (transportTuple (reflect s E M) X.2 i)) _
  rw [tsupport_transportTuple_reflect]
  exact (disjoint_preimage_positiveSide s E M).mono (Set.preimage_mono (hX.2 i)) (hY.2 j)
def reflectAppend (E : Ambient) (M : AmbientMirror E)
    (X Y : separatedIn (positiveSide s E M)) : allSeparatedTuples s E :=
  ⟨tupleAppend (reflectTuple s E M X.1) Y.1, reflectAppend_mem s E M X.2 Y.2⟩
def gramSum (E : Ambient) (M : AmbientMirror E) (σ : allSeparatedTuples s E → ℝ) {r : ℕ}
    (X : Fin r → separatedIn (positiveSide s E M)) (c : Fin r → ℂ) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (σ (reflectAppend s E M (X i) (X j)) : ℂ)
def IsReflectionPositive (E : Ambient) (M : AmbientMirror E)
    (σ : allSeparatedTuples s E → ℝ) : Prop :=
  ∀ (r : ℕ) (X : Fin r → separatedIn (positiveSide s E M)) (c : Fin r → ℂ),
    (gramSum s E M σ X c).im = 0 ∧ 0 ≤ (gramSum s E M σ X c).re
end AmbientMirror
end YangMills.Construction.AmbientPoints
