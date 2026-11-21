import YangMills.Construction.ChessboardTori.CoveringMapOnTheCellsOfAGridProof
import YangMills.Construction.ToriAtArbitraryCouplings.TheSpaceAndTheCubeSize
import Mathlib
import YangMills.Construction.Torus.CollinearQuadruplesProof
import YangMills.Construction.Torus.GeometryTransportLiftAndDilationOfTestPairsProof
set_option autoImplicit false

section
open Set
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings.DistanceAndProjection
open TorusMetric (euclidNormVec)
open MetricNotions (IsContinuousWrt IsOpenWrt)
def DistanceIsLeastAndLiftsExist (s : TorusSide) : Prop :=
  (∀ u v : Fin 4 → ℝ,
    IsLeast (range fun k : Fin 4 → ℤ => euclidNormVec (u - v - TestFunctions.latticeTranslate s.length k))
      (s.pointDist .torus (s.proj u) (s.proj v))) ∧
  (∀ (E : ReflectionPositivity.AxisMirror.Ambient) (u v : Fin 4 → ℝ),
    s.pointDist E (s.ambientProj E u) (s.ambientProj E v) ≤ euclidNormVec (u - v)) ∧
  ∀ (E : ReflectionPositivity.AxisMirror.Ambient) (x y : s.Point E) (u : Fin 4 → ℝ),
    s.ambientProj E u = x →
    ∃ v : Fin 4 → ℝ, s.ambientProj E v = y ∧ euclidNormVec (u - v) = s.pointDist E x y
def IsMetric (s : TorusSide) : Prop :=
  ∀ (E : ReflectionPositivity.AxisMirror.Ambient) (x y z : s.Point E),
    s.pointDist E x y = s.pointDist E y x ∧
    (s.pointDist E x y = 0 → x = y) ∧
    s.pointDist E x z ≤ s.pointDist E x y + s.pointDist E y z
def ProjContinuousOpenSurjective (s : TorusSide) : Prop :=
  (∀ E : ReflectionPositivity.AxisMirror.Ambient,
    IsContinuousWrt InfiniteLattice.euclidDist (s.pointDist E) (s.ambientProj E) ∧
    Function.Surjective (s.ambientProj E) ∧
    (∀ O : Set (Fin 4 → ℝ), IsOpenWrt InfiniteLattice.euclidDist O →
      s.IsOpenWrt E (s.ambientProj E '' O)) ∧
    ∀ (𝕜 : Type) [RCLike 𝕜] (h : s.Point E → 𝕜),
      IsContinuousWrt InfiniteLattice.euclidDist (fun a b : 𝕜 => ‖a - b‖) (s.pullback h) →
        s.IsContinuousWrt E h) ∧
  s.proj '' (pi univ fun _ => Icc 0 s.length) = univ ∧
  s.IsCompactWrt .torus univ
def IsometricOnSmallSets (s : TorusSide) : Prop :=
  ∀ S : Set (Fin 4 → ℝ), (∀ u ∈ S, ∀ v ∈ S, euclidNormVec (u - v) ≤ s.length / 2) →
    (∀ u ∈ S, ∀ v ∈ S,
      s.pointDist .torus (s.proj u) (s.proj v) = euclidNormVec (u - v)) ∧
    InjOn s.proj S ∧
    (∀ k : Fin 4 → ℤ, k ≠ 0 →
      S ∩ (fun v => v + TestFunctions.latticeTranslate s.length k) '' S = ∅) ∧
    ∀ A A' : Set (Fin 4 → ℝ), A ⊆ S → A' ⊆ S →
      s.setDist .torus (s.proj '' A) (s.proj '' A') =
        s.setDist .euclidean A A'
def DisjointCompactSeparated (s : TorusSide) : Prop :=
  ∀ (E : ReflectionPositivity.AxisMirror.Ambient) (Z Z' : Set (s.Point E)),
    s.IsCompactWrt E Z → s.IsCompactWrt E Z' → Disjoint Z Z' → s.PositivelySeparated E Z Z'
def FullStatement : Prop :=
  ∀ s : TorusSide, DistanceIsLeastAndLiftsExist s ∧ IsMetric s ∧ ProjContinuousOpenSurjective s ∧
    IsometricOnSmallSets s ∧ DisjointCompactSeparated s
end YangMills.Construction.ToriAtArbitraryCouplings.DistanceAndProjection
end
end

open Set
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings.DistanceAndProjection
open TorusMetric (euclidNormVec torusProj torusEuclidNorm Torus4)
open TestFunctions (latticeTranslate)
open MetricNotions (IsContinuousWrt IsOpenWrt IsCompactWrt)
theorem euclidNormVec_nonneg (w : Fin 4 → ℝ) : 0 ≤ euclidNormVec w := Real.sqrt_nonneg _
theorem euclidNormVec_sub_le (a b : Fin 4 → ℝ) :
    euclidNormVec (a - b) ≤ euclidNormVec a + euclidNormVec b := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.euclidNormVec_sub_le <;> assumption
theorem euclidNormVec_sub_comm (a b : Fin 4 → ℝ) :
    euclidNormVec (a - b) = euclidNormVec (b - a) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
theorem euclidNormVec_zero : euclidNormVec 0 = 0 := by simp [euclidNormVec]
theorem abs_apply_le_euclidNormVec (w : Fin 4 → ℝ) (i : Fin 4) : |w i| ≤ euclidNormVec w := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem eq_of_euclidNormVec_sub_eq_zero {a b : Fin 4 → ℝ} (h : euclidNormVec (a - b) = 0) :
    a = b := by apply _root_.YangMills.Construction.AmbientPoints.eq_of_euclidNormVec_sub_eq_zero <;> assumption
theorem euclidNormVec_le_of_abs_le {a b : Fin 4 → ℝ} (h : ∀ i, |a i| ≤ |b i|) :
    euclidNormVec a ≤ euclidNormVec b := by apply _root_.YangMills.Construction.ChessboardTori.ProjOnGridCellsProof.euclidNormVec_mono <;> assumption
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
section Torus
variable {ℓ : ℝ}
theorem torusProj_sub (a b : Fin 4 → ℝ) : torusProj ℓ a - torusProj ℓ b = torusProj ℓ (a - b) := by apply _root_.YangMills.SharedProofs.p13492 <;> assumption
theorem torusProj_sub_latticeTranslate (w : Fin 4 → ℝ) (n : Fin 4 → ℤ) :
    torusProj ℓ (w - latticeTranslate ℓ n) = torusProj ℓ w := by apply _root_.YangMills.Construction.TestFunctions.PairTransport.torusProj_sub_latticeTranslate <;> assumption
theorem latticeTranslate_zero : latticeTranslate ℓ 0 = 0 := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.latticeTranslate_zero <;> assumption
theorem exists_nearest_translate (hℓ : 0 < ℓ) (w : Fin 4 → ℝ) :
    ∃ n₀ : Fin 4 → ℤ, ∀ n : Fin 4 → ℤ,
      euclidNormVec (w - latticeTranslate ℓ n₀) ≤ euclidNormVec (w - latticeTranslate ℓ n) := by
  refine ⟨fun i => round (w i / ℓ), fun n => euclidNormVec_le_of_abs_le fun i => ?_⟩
  have h := round_le (w i / ℓ) (n i)
  have e : ∀ z : ℤ, |w i - ℓ * z| = ℓ * |w i / ℓ - z| := by
    intro z
    have hz : w i - ℓ * z = ℓ * (w i / ℓ - z) := by
      field_simp
    rw [hz, abs_mul, abs_of_pos hℓ]
  simp only [Pi.sub_apply, latticeTranslate]
  rw [e, e]
  exact mul_le_mul_of_nonneg_left h hℓ.le
theorem isLeast_torusEuclidNorm (hℓ : 0 < ℓ) (w : Fin 4 → ℝ) :
    IsLeast (range fun n : Fin 4 → ℤ => euclidNormVec (w - latticeTranslate ℓ n))
      (torusEuclidNorm (torusProj ℓ w)) := by
  have hset : euclidNormVec '' (torusProj ℓ ⁻¹' {torusProj ℓ w}) =
      range fun n : Fin 4 → ℤ => euclidNormVec (w - latticeTranslate ℓ n) := by
    ext t
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨n, rfl⟩ :=
        TestFunctions.exists_latticeTranslate_of_torusProj_eq
          (show torusProj ℓ v = torusProj ℓ w from hv)
      refine ⟨-n, ?_⟩
      have e : w - latticeTranslate ℓ (-n) = w + latticeTranslate ℓ n := by
        funext i
        simp [latticeTranslate]
      simp only [e]
    · rintro ⟨n, rfl⟩
      exact ⟨_, torusProj_sub_latticeTranslate w n, rfl⟩
  obtain ⟨n₀, hn₀⟩ := exists_nearest_translate hℓ w
  have hl : IsLeast (range fun n : Fin 4 → ℤ => euclidNormVec (w - latticeTranslate ℓ n))
      (euclidNormVec (w - latticeTranslate ℓ n₀)) :=
    ⟨⟨n₀, rfl⟩, by rintro _ ⟨n, rfl⟩; exact hn₀ n⟩
  have e : torusEuclidNorm (torusProj ℓ w) = euclidNormVec (w - latticeTranslate ℓ n₀) := by
    rw [torusEuclidNorm, hset]
    exact hl.csInf_eq
  rw [e]
  exact hl
theorem isLeast_torusEuclidNorm_sub (hℓ : 0 < ℓ) (a b : Fin 4 → ℝ) :
    IsLeast (range fun n : Fin 4 → ℤ => euclidNormVec (a - b - latticeTranslate ℓ n))
      (torusEuclidNorm (torusProj ℓ a - torusProj ℓ b)) := by
  rw [torusProj_sub]
  exact isLeast_torusEuclidNorm hℓ (a - b)
theorem torusEuclidNorm_sub_le (hℓ : 0 < ℓ) (a b : Fin 4 → ℝ) :
    torusEuclidNorm (torusProj ℓ a - torusProj ℓ b) ≤ euclidNormVec (a - b) :=
  (isLeast_torusEuclidNorm_sub hℓ a b).2 ⟨0, by simp [latticeTranslate_zero]⟩
theorem exists_lift_realizing (hℓ : 0 < ℓ) (x y : Torus4 ℓ) (a : Fin 4 → ℝ)
    (ha : torusProj ℓ a = x) :
    ∃ b : Fin 4 → ℝ, torusProj ℓ b = y ∧ euclidNormVec (a - b) = torusEuclidNorm (x - y) := by
  obtain ⟨b₀, rfl⟩ := TestFunctions.torusProj_surjective ℓ y
  subst ha
  obtain ⟨n, hn⟩ := (isLeast_torusEuclidNorm_sub hℓ a b₀).1
  refine ⟨b₀ + latticeTranslate ℓ n, TestFunctions.torusProj_add_latticeTranslate ℓ b₀ n, ?_⟩
  rw [← hn, sub_add_eq_sub_sub]
theorem torusProj_image_cube (hℓ : 0 < ℓ) :
    torusProj ℓ '' (pi univ fun _ => Icc 0 ℓ) = univ := by
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨w, rfl⟩ := TestFunctions.torusProj_surjective ℓ x
  refine ⟨w - latticeTranslate ℓ fun i => ⌊w i / ℓ⌋, ?_, torusProj_sub_latticeTranslate w _⟩
  intro i _
  have h1 := Int.floor_le (w i / ℓ)
  have h2 := Int.lt_floor_add_one (w i / ℓ)
  rw [le_div_iff₀ hℓ] at h1
  rw [div_lt_iff₀ hℓ] at h2
  simp only [Pi.sub_apply, latticeTranslate, mem_Icc]
  constructor <;> nlinarith
theorem half_le_euclidNormVec_sub_translate (hℓ : 0 < ℓ) {a b : Fin 4 → ℝ}
    (hab : euclidNormVec (a - b) ≤ ℓ / 2) {n : Fin 4 → ℤ} (hn : n ≠ 0) :
    ℓ / 2 ≤ euclidNormVec (a - b - latticeTranslate ℓ n) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
  have h1 : (1 : ℝ) ≤ |(n i : ℝ)| := by
    exact_mod_cast Int.one_le_abs (by simpa using hi)
  have h2 : ℓ ≤ euclidNormVec (latticeTranslate ℓ n) := by
    have h := abs_apply_le_euclidNormVec (latticeTranslate ℓ n) i
    simp only [latticeTranslate, abs_mul, abs_of_pos hℓ] at h
    nlinarith
  have h3 := euclidNormVec_sub_le (a - b) (a - b - latticeTranslate ℓ n)
  rw [sub_sub_cancel] at h3
  linarith
theorem isometry_on_small_sets (hℓ : 0 < ℓ) (S : Set (Fin 4 → ℝ))
    (hS : ∀ a ∈ S, ∀ b ∈ S, euclidNormVec (a - b) ≤ ℓ / 2) :
    (∀ a ∈ S, ∀ b ∈ S, torusEuclidNorm (torusProj ℓ a - torusProj ℓ b) = euclidNormVec (a - b)) ∧
    InjOn (torusProj ℓ) S ∧
    (∀ n : Fin 4 → ℤ, n ≠ 0 → S ∩ (fun b => b + latticeTranslate ℓ n) '' S = ∅) ∧
    ∀ A B : Set (Fin 4 → ℝ), A ⊆ S → B ⊆ S →
      TorusMetric.setEuclidDist (torusProj ℓ '' A) (torusProj ℓ '' B) =
        TestFunctions.setDistR4 A B := by
  have hiso : ∀ a ∈ S, ∀ b ∈ S,
      torusEuclidNorm (torusProj ℓ a - torusProj ℓ b) = euclidNormVec (a - b) := by
    intro a ha b hb
    refine le_antisymm (torusEuclidNorm_sub_le hℓ a b) ?_
    obtain ⟨n, hn⟩ := (isLeast_torusEuclidNorm_sub hℓ a b).1
    rw [← hn]
    by_cases h0 : n = 0
    · subst h0
      simp [latticeTranslate_zero]
    · exact (hS a ha b hb).trans (half_le_euclidNormVec_sub_translate hℓ (hS a ha b hb) h0)
  refine ⟨hiso, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have h := hiso a ha b hb
    have h0 : torusEuclidNorm (torusProj ℓ a - torusProj ℓ b) ≤ 0 := by
      have h1 := torusEuclidNorm_sub_le (ℓ := ℓ) hℓ b b
      rw [hab]
      simpa [euclidNormVec_zero] using h1
    exact eq_of_euclidNormVec_sub_eq_zero (le_antisymm (h ▸ h0) (euclidNormVec_nonneg _))
  · intro n hn
    refine eq_empty_of_forall_notMem ?_
    rintro a ⟨ha, b, hb, rfl⟩
    have h := half_le_euclidNormVec_sub_translate hℓ (hS _ ha b hb) hn
    have e : b + latticeTranslate ℓ n - b - latticeTranslate ℓ n = 0 := by abel
    rw [e, euclidNormVec_zero] at h
    linarith
  · intro A B hA hB
    simp only [TorusMetric.setEuclidDist, TestFunctions.setDistR4, iInf_image]
    refine iInf_congr fun a => iInf_congr fun ha => iInf_congr fun b => iInf_congr fun hb => ?_
    rw [hiso a (hA ha) b (hB hb)]
end Torus
theorem induction_on_compact {X : Type*} (d : X → X → ℝ) {Z : Set X} (hZ : IsCompactWrt d Z)
    (Q : Set X → Prop) (h0 : Q ∅) (hunion : ∀ A B, Q A → Q B → Q (A ∪ B))
    (hmono : ∀ A B, A ⊆ B → Q B → Q A)
    (hloc : ∀ x ∈ Z, ∃ U, IsOpenWrt d U ∧ x ∈ U ∧ Q U) : Q Z := by
  have key : ∀ 𝒱 : Set (Set X), 𝒱.Finite → (∀ U ∈ 𝒱, Q U) → Q (⋃₀ 𝒱) := by
    intro 𝒱 hf
    induction 𝒱, hf using Set.Finite.induction_on with
    | empty =>
      intro _
      simpa using h0
    | @insert a s _ _ ih =>
      intro h
      rw [sUnion_insert]
      exact hunion _ _ (h a (mem_insert _ _)) (ih fun U hU => h U (mem_insert_of_mem _ hU))
  obtain ⟨𝒰', hsub, hfin, hcov⟩ := hZ {U | IsOpenWrt d U ∧ Q U} (fun U hU => hU.1) (fun x hx => by
    obtain ⟨U, hU, hxU, hQ⟩ := hloc x hx
    exact ⟨U, ⟨hU, hQ⟩, hxU⟩)
  exact hmono _ _ hcov (key _ hfin fun U hU => (hsub hU).2)
structure ProjectedMetric {P : Type*} (d : P → P → ℝ) (π : (Fin 4 → ℝ) → P) : Prop where
  dist_le : ∀ a b, d (π a) (π b) ≤ euclidNormVec (a - b)
  exists_lift : ∀ x y a, π a = x → ∃ b, π b = y ∧ euclidNormVec (a - b) = d x y
  surjective : Function.Surjective π
namespace ProjectedMetric
variable {P : Type*} {d : P → P → ℝ} {π : (Fin 4 → ℝ) → P}
theorem nonneg (h : ProjectedMetric d π) (x y : P) : 0 ≤ d x y := by
  obtain ⟨a, rfl⟩ := h.surjective x
  obtain ⟨b, -, hb⟩ := h.exists_lift _ y a rfl
  exact hb ▸ euclidNormVec_nonneg _
theorem dist_self (h : ProjectedMetric d π) (x : P) : d x x = 0 := by
  obtain ⟨a, rfl⟩ := h.surjective x
  refine le_antisymm ?_ (h.nonneg _ _)
  simpa [euclidNormVec_zero] using h.dist_le a a
theorem comm (h : ProjectedMetric d π) (x y : P) : d x y = d y x := by
  have key : ∀ x y, d y x ≤ d x y := by
    intro x y
    obtain ⟨a, rfl⟩ := h.surjective x
    obtain ⟨b, rfl, hb⟩ := h.exists_lift _ y a rfl
    rw [← hb, euclidNormVec_sub_comm]
    exact h.dist_le b a
  exact le_antisymm (key y x) (key x y)
theorem eq_of_dist_eq_zero (h : ProjectedMetric d π) {x y : P} (hxy : d x y = 0) : x = y := by
  obtain ⟨a, rfl⟩ := h.surjective x
  obtain ⟨b, rfl, hb⟩ := h.exists_lift _ y a rfl
  rw [eq_of_euclidNormVec_sub_eq_zero (hb.trans hxy)]
theorem triangle (h : ProjectedMetric d π) (x y z : P) : d x z ≤ d x y + d y z := by
  obtain ⟨a, rfl⟩ := h.surjective x
  obtain ⟨b, rfl, hb⟩ := h.exists_lift _ y a rfl
  obtain ⟨c, rfl, hc⟩ := h.exists_lift _ z b rfl
  rw [← hb, ← hc]
  refine (h.dist_le a c).trans ?_
  have e := euclidNormVec_sub_le (a - b) (c - b)
  rw [sub_sub_sub_cancel_right, euclidNormVec_sub_comm c b] at e
  exact e
theorem isOpen_ball (h : ProjectedMetric d π) (x : P) (r : ℝ) : IsOpenWrt d {y | d x y < r} := by
  intro y hy
  have hy' : d x y < r := hy
  refine ⟨r - d x y, sub_pos.mpr hy', fun z hz => ?_⟩
  have h1 := h.triangle x y z
  show d x z < r
  linarith
theorem continuous (h : ProjectedMetric d π) : IsContinuousWrt InfiniteLattice.euclidDist d π :=
  fun a ε hε => ⟨ε, hε, fun b hb => (h.dist_le a b).trans_lt hb⟩
theorem isOpen_image (h : ProjectedMetric d π) {O : Set (Fin 4 → ℝ)}
    (hO : IsOpenWrt InfiniteLattice.euclidDist O) : IsOpenWrt d (π '' O) := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨r, hr, hrO⟩ := hO a ha
  refine ⟨r, hr, fun y hy => ?_⟩
  obtain ⟨b, rfl, hb⟩ := h.exists_lift _ y a rfl
  exact ⟨b, hrO b (hb.trans_lt hy), rfl⟩
theorem continuous_of_comp (h : ProjectedMetric d π) {𝕜 : Type} [RCLike 𝕜] (f : P → 𝕜)
    (hf : IsContinuousWrt InfiniteLattice.euclidDist (fun s t : 𝕜 => ‖s - t‖) (f ∘ π)) :
    IsContinuousWrt d (fun s t : 𝕜 => ‖s - t‖) f := by
  intro x ε hε
  obtain ⟨a, rfl⟩ := h.surjective x
  obtain ⟨δ, hδ, hf'⟩ := hf a ε hε
  refine ⟨δ, hδ, fun y hy => ?_⟩
  obtain ⟨b, rfl, hb⟩ := h.exists_lift _ y a rfl
  exact hf' b (hb.trans_lt hy)
theorem isCompact_univ (h : ProjectedMetric d π) {K : Set (Fin 4 → ℝ)} (hK : IsCompact K)
    (hcube : π '' K = univ) : IsCompactWrt d (univ : Set P) := by
  intro 𝒰 hU hcov
  have hopen : ∀ U ∈ 𝒰, IsOpen (π ⁻¹' U) := by
    intro U hUU
    rw [isOpen_iff_mem_nhds]
    intro a ha
    obtain ⟨r, hr, hrU⟩ := hU U hUU (π a) ha
    have hc : Continuous fun b : Fin 4 → ℝ => euclidNormVec (b - a) :=
      continuous_euclidNormVec.comp (continuous_id.sub continuous_const)
    have hball : {b | euclidNormVec (b - a) < r} ∈ nhds a :=
      (isOpen_lt hc continuous_const).mem_nhds (by simpa [euclidNormVec_zero] using hr)
    filter_upwards [hball] with b hb
    refine hrU _ ((h.dist_le a b).trans_lt ?_)
    rw [euclidNormVec_sub_comm]
    exact hb
  obtain ⟨t, ht, hfin, hKt⟩ := hK.elim_finite_subcover_image hopen (fun a _ => by
    obtain ⟨U, hUU, hx⟩ := hcov (mem_univ (π a))
    exact mem_biUnion hUU hx)
  refine ⟨t, ht, hfin, fun x _ => ?_⟩
  have hx : x ∈ π '' K := hcube ▸ mem_univ x
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨U, hUt, hU'⟩ := mem_iUnion₂.mp (hKt ha)
  exact ⟨U, hUt, hU'⟩
theorem exists_sep (h : ProjectedMetric d π) {Z Z' : Set P} (hZ : IsCompactWrt d Z)
    (hZ' : IsCompactWrt d Z') (hdis : Disjoint Z Z') :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Z, ∀ y ∈ Z', r ≤ d x y := by
  have pointwise : ∀ x, x ∉ Z' → ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Z', r ≤ d x y := by
    intro x hx
    refine induction_on_compact d hZ' (fun A => ∃ r : ℝ, 0 < r ∧ ∀ y ∈ A, r ≤ d x y)
      ⟨1, one_pos, by simp⟩ ?_ ?_ ?_
    · rintro A B ⟨s, hs, hA⟩ ⟨t, ht, hB⟩
      refine ⟨min s t, lt_min hs ht, ?_⟩
      rintro y (hy | hy)
      · exact (min_le_left _ _).trans (hA y hy)
      · exact (min_le_right _ _).trans (hB y hy)
    · rintro A B hAB ⟨t, ht, hB⟩
      exact ⟨t, ht, fun y hy => hB y (hAB hy)⟩
    · intro y hy
      have hpos : 0 < d x y := lt_of_le_of_ne (h.nonneg x y) fun e =>
        hx ((h.eq_of_dist_eq_zero e.symm) ▸ hy)
      refine ⟨{z | d y z < d x y / 2}, h.isOpen_ball y _, ?_, d x y / 2, half_pos hpos, ?_⟩
      · show d y y < _
        rw [h.dist_self]
        exact half_pos hpos
      · intro z hz
        have hz' : d y z < d x y / 2 := hz
        have h1 := h.triangle x z y
        have h2 := h.comm z y
        linarith
  refine induction_on_compact d hZ (fun A => ∃ r : ℝ, 0 < r ∧ ∀ x ∈ A, ∀ y ∈ Z', r ≤ d x y)
    ⟨1, one_pos, by simp⟩ ?_ ?_ ?_
  · rintro A B ⟨s, hs, hA⟩ ⟨t, ht, hB⟩
    refine ⟨min s t, lt_min hs ht, ?_⟩
    rintro x (hx | hx) y hy
    · exact (min_le_left _ _).trans (hA x hx y hy)
    · exact (min_le_right _ _).trans (hB x hx y hy)
  · rintro A B hAB ⟨t, ht, hB⟩
    exact ⟨t, ht, fun x hx => hB x (hAB hx)⟩
  · intro x hx
    obtain ⟨r, hr, hxr⟩ := pointwise x fun hx' => Set.disjoint_left.mp hdis hx hx'
    refine ⟨{z | d x z < r / 2}, h.isOpen_ball x _, ?_, r / 2, half_pos hr, ?_⟩
    · show d x x < _
      rw [h.dist_self]
      exact half_pos hr
    · intro z hz y hy
      have hz' : d x z < r / 2 := hz
      have h1 := h.triangle x z y
      have h2 := hxr y hy
      linarith
end ProjectedMetric
theorem length_pos (s : TorusSide) : 0 < s.length := by
  have hL : (0 : ℝ) < s.L := by
    have h := s.admissible.2
    exact_mod_cast (by omega : 0 < s.L)
  simp only [TorusSide.length, PeriodicLattice.torusSide]
  positivity
theorem projectedMetric_torus {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ProjectedMetric (fun x y : Torus4 ℓ => torusEuclidNorm (x - y)) (torusProj ℓ) :=
  ⟨torusEuclidNorm_sub_le hℓ, exists_lift_realizing hℓ, TestFunctions.torusProj_surjective ℓ⟩
theorem projectedMetric_euclid :
    ProjectedMetric InfiniteLattice.euclidDist (id : (Fin 4 → ℝ) → Fin 4 → ℝ) :=
  ⟨fun _ _ => le_rfl, fun x y a ha => ⟨y, rfl, by subst ha; rfl⟩, Function.surjective_id⟩
theorem projectedMetric (s : TorusSide) (E : ReflectionPositivity.AxisMirror.Ambient) :
    ProjectedMetric (s.pointDist E) (s.ambientProj E) := by
  cases E
  · exact projectedMetric_torus (length_pos s)
  · exact projectedMetric_euclid
theorem disjointCompactSeparated (s : TorusSide) : DisjointCompactSeparated s := by
  intro E Z Z' hZ hZ' hdis
  obtain ⟨r, hr, hgap⟩ := (projectedMetric s E).exists_sep hZ hZ' hdis
  have hbound : ENNReal.ofReal r ≤ s.setDist E Z Z' := by
    cases E
    · exact le_iInf₂ fun x hx => le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal (hgap x hx y hy)
    · exact le_iInf₂ fun x hx => le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal (hgap x hx y hy)
  exact (ENNReal.ofReal_pos.mpr hr).trans_le hbound
theorem fullStatement_holds : FullStatement := by
  intro s
  have hℓ := length_pos s
  refine ⟨⟨fun a b => isLeast_torusEuclidNorm_sub hℓ a b, fun E a b => (projectedMetric s E).dist_le a b,
    fun E x y a ha => (projectedMetric s E).exists_lift x y a ha⟩, fun E x y z =>
    ⟨(projectedMetric s E).comm x y, (projectedMetric s E).eq_of_dist_eq_zero,
      (projectedMetric s E).triangle x y z⟩,
    ⟨fun E => ⟨(projectedMetric s E).continuous, (projectedMetric s E).surjective,
      fun O hO => (projectedMetric s E).isOpen_image hO,
      fun 𝕜 _ f hf => (projectedMetric s E).continuous_of_comp f hf⟩, torusProj_image_cube hℓ,
      (projectedMetric s .torus).isCompact_univ (isCompact_univ_pi fun _ => isCompact_Icc)
        (torusProj_image_cube hℓ)⟩,
    fun S hS => isometry_on_small_sets hℓ S hS, disjointCompactSeparated s⟩
end YangMills.Construction.ToriAtArbitraryCouplings.DistanceAndProjection
end
