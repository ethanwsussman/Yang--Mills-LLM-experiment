import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.InfiniteLattice.MultilinearityOfTheConnectedCurvatureFunctions
import YangMills.Construction.InfiniteLattice.StatesAtFixedSpacing
import YangMills.Construction.InfiniteLattice.TransportOfLipschitzFunctionsAtAPositiveMargin
import YangMills.Construction.ParameterData.TheWindowHasMembers
import YangMills.Construction.SystemOfAdmissibleConstants.LimitsAlongFirstPassageData
import YangMills.Construction.SystemOfAdmissibleConstants.SubsequenceAtEveryTuple
import YangMills.Construction.SystemOfAdmissibleConstants.TheFourBoundsAlongTheTrajectory
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Filter Set TopologicalSpace MeasureTheory AmbientPoints
open scoped Topology
open TorusMetric (euclidNormVec torusEuclidNorm setEuclidDist torusProj Torus4)
open TestFunctions
namespace SystemOfAdmissibleConstants.TrajectoryLimits
abbrev FourVec : Type := Fin 4 → ℝ
theorem norm_le_euclidNormVec (v : FourVec) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
theorem euclidNormVec_le_two_mul_norm (v : FourVec) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
def C1Bounded (g : FourVec → ℝ) (b : ℝ) : Prop := ∀ x, |g x| ≤ b ∧ ‖fderiv ℝ g x‖ ≤ b
theorem C1Bounded.nonneg {g : FourVec → ℝ} {b : ℝ} (h : C1Bounded g b) : 0 ≤ b :=
  (abs_nonneg _).trans (h 0).1
theorem C1Bounded.mono {g : FourVec → ℝ} {b b' : ℝ} (h : C1Bounded g b) (hb : b ≤ b') :
    C1Bounded g b' :=
  fun x => ⟨(h x).1.trans hb, (h x).2.trans hb⟩
theorem C1Bounded.of_sub {f h : FourVec → ℝ} (hf : ContDiff ℝ 1 f) (hh : ContDiff ℝ 1 h)
    {b ε : ℝ} (h₁ : C1Bounded f b) (h₂ : C1Bounded (f - h) ε) : C1Bounded h (b + ε) := by
  intro x
  constructor
  · have e : h x = f x - (f - h) x := by simp
    rw [e]
    exact (abs_sub _ _).trans (add_le_add (h₁ x).1 (h₂ x).1)
  · have e : fderiv ℝ (f - h) x = fderiv ℝ f x - fderiv ℝ h x :=
      fderiv_sub ((hf.differentiable (by norm_num)) x) ((hh.differentiable (by norm_num)) x)
    have e' : fderiv ℝ h x = fderiv ℝ f x - fderiv ℝ (f - h) x := by rw [e]; abel
    rw [e']
    exact (norm_sub_le _ _).trans (add_le_add (h₁ x).2 (h₂ x).2)
theorem c1Bounded_sub {f h : FourVec → ℝ} (hf : ContDiff ℝ 1 f) (hh : ContDiff ℝ 1 h) {ε : ℝ}
    (hc : ∀ x, |f x - h x| ≤ ε ∧ ‖fderiv ℝ f x - fderiv ℝ h x‖ ≤ ε) : C1Bounded (f - h) ε := by
  intro x
  have e : fderiv ℝ (f - h) x = fderiv ℝ f x - fderiv ℝ h x :=
    fderiv_sub ((hf.differentiable (by norm_num)) x) ((hh.differentiable (by norm_num)) x)
  rw [e]
  exact hc x
theorem norm_sub_le_of_c1Bounded {g : FourVec → ℝ} (hg : ContDiff ℝ 1 g) {b : ℝ} (hb : C1Bounded g b)
    (x y : FourVec) : ‖g x - g y‖ ≤ b * euclidNormVec (x - y) := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := g) (s := univ) (C := b)
    (x := y) (y := x) (fun z _ => (hg.differentiable (by norm_num)) z)
    (fun z _ => (hb z).2) convex_univ (mem_univ _) (mem_univ _)
  exact h.trans (mul_le_mul_of_nonneg_left (norm_le_euclidNormVec _) hb.nonneg)
theorem exists_countable_c1_approx {Q : Set FourVec} (hQ : IsCompact Q) (S : Set (FourVec → ℝ))
    (hS : ∀ g ∈ S, ContDiff ℝ 1 g)
    (hz : ∀ x, ∃ y ∈ Q, ∀ g ∈ S, g x = g y ∧ fderiv ℝ g x = fderiv ℝ g y) :
    ∃ D : Set (FourVec → ℝ), D.Countable ∧ D ⊆ S ∧ ∀ g ∈ S, ∀ ε : ℝ, 0 < ε → ∃ h ∈ D,
      ∀ x, |g x - h x| ≤ ε ∧ ‖fderiv ℝ g x - fderiv ℝ h x‖ ≤ ε := by
  have : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  let jet : S → C(Q, ℝ × (FourVec →L[ℝ] ℝ)) := fun g =>
    ⟨fun x => (g.1 x.1, fderiv ℝ g.1 x.1),
      (((hS g.1 g.2).continuous.comp continuous_subtype_val).prodMk
        (((hS g.1 g.2).continuous_fderiv (by norm_num)).comp continuous_subtype_val))⟩
  have hs : IsSeparable (range jet) := IsSeparable.of_separableSpace _
  obtain ⟨t, hts, htc, hdense⟩ := hs.exists_countable_dense_subset
  have hpre : ∀ y : t, ∃ g : S, jet g = y.1 := fun y => hts y.2
  choose g hg using hpre
  have := htc.to_subtype
  refine ⟨range fun y : t => (g y).1, countable_range _, ?_, fun f hf ε hε => ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact (g y).2
  · obtain ⟨y, hy, hd⟩ := (Metric.mem_closure_iff (α := C(Q, ℝ × (FourVec →L[ℝ] ℝ)))).1
      (hdense ⟨⟨f, hf⟩, rfl⟩) ε hε
    refine ⟨(g ⟨y, hy⟩).1, ⟨⟨y, hy⟩, rfl⟩, fun x => ?_⟩
    set h := (g ⟨y, hy⟩).1 with hh
    have hhS : h ∈ S := (g ⟨y, hy⟩).2
    obtain ⟨x', hx', hxx⟩ := hz x
    have h₁ : dist (jet ⟨f, hf⟩ ⟨x', hx'⟩) (y ⟨x', hx'⟩) < ε :=
      (ContinuousMap.dist_apply_le_dist _).trans_lt hd
    have hyx : y ⟨x', hx'⟩ = (h x', fderiv ℝ h x') := by
      have := hg ⟨y, hy⟩
      rw [← show jet (g ⟨y, hy⟩) = y from this]
      rfl
    rw [hyx] at h₁
    have h₃ : max (dist (f x') (h x')) (dist (fderiv ℝ f x') (fderiv ℝ h x')) < ε := h₁
    obtain ⟨a₁, a₂⟩ := hxx f hf
    obtain ⟨b₁, b₂⟩ := hxx h hhS
    rw [a₁, b₁, a₂, b₂]
    constructor
    · have := (le_max_left _ _).trans_lt h₃
      rw [Real.dist_eq] at this
      exact this.le
    · have := (le_max_right _ _).trans_lt h₃
      rw [dist_eq_norm] at this
      exact this.le
def c1SupportedIn (A : Set FourVec) : Set (FourVec → ℝ) :=
  {f | ContDiff ℝ 1 f ∧ tsupport f ⊆ A}
theorem apply_eq_zero_of_notMem {A : Set FourVec} {f : FourVec → ℝ} (hf : f ∈ c1SupportedIn A)
    {x : FourVec} (hx : x ∉ A) : f x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (hf.2 h)
theorem fderiv_eq_zero_of_notMem {A : Set FourVec} {f : FourVec → ℝ} (hf : f ∈ c1SupportedIn A)
    {x : FourVec} (hx : x ∉ A) : fderiv ℝ f x = 0 :=
  fderiv_of_notMem_tsupport ℝ fun h => hx (hf.2 h)
theorem exists_c1Bounded_of_isCompact {A : Set FourVec} (hA : IsCompact A) {f : FourVec → ℝ}
    (hf : f ∈ c1SupportedIn A) : ∃ b, C1Bounded f b := by
  have hK : IsCompact (tsupport f) := hA.of_isClosed_subset (isClosed_tsupport _) hf.2
  obtain ⟨b₁, h₁⟩ := (show HasCompactSupport f from hK).exists_bound_of_continuous hf.1.continuous
  have hd : HasCompactSupport (fderiv ℝ f) := (show HasCompactSupport f from hK).fderiv (𝕜 := ℝ)
  obtain ⟨b₂, h₂⟩ := hd.exists_bound_of_continuous (hf.1.continuous_fderiv (by norm_num))
  exact ⟨max b₁ b₂, fun x => ⟨(h₁ x).trans (le_max_left _ _), (h₂ x).trans (le_max_right _ _)⟩⟩
theorem exists_countable_c1SupportedIn {A : Set FourVec} (hA : IsCompact A) :
    ∃ D : Set (FourVec → ℝ), D.Countable ∧ D ⊆ c1SupportedIn A ∧
      ∀ f ∈ c1SupportedIn A, ∀ ε : ℝ, 0 < ε → ∃ h ∈ D, C1Bounded (f - h) ε := by
  obtain ⟨r, hr⟩ := hA.isBounded.subset_closedBall (0 : FourVec)
  set r' : ℝ := |r| + 1 with hr'
  have hr0 : 0 < r' := by positivity
  have hrr : r < r' := by linarith [le_abs_self r]
  have hy₀ : ‖(fun _ => r' : FourVec)‖ = r' := by
    rw [pi_norm_const, Real.norm_eq_abs, abs_of_pos hr0]
  have hz : ∀ x, ∃ y ∈ Metric.closedBall (0 : FourVec) r', ∀ g ∈ c1SupportedIn A,
      g x = g y ∧ fderiv ℝ g x = fderiv ℝ g y := by
    intro x
    have hnotA : ∀ z : FourVec, r' ≤ ‖z‖ → z ∉ A := fun z hz hzA => by
      have h := hr hzA
      rw [mem_closedBall_zero_iff] at h
      linarith
    by_cases hx : x ∈ Metric.closedBall (0 : FourVec) r'
    · exact ⟨x, hx, fun _ _ => ⟨rfl, rfl⟩⟩
    · refine ⟨fun _ => r', mem_closedBall_zero_iff.2 hy₀.le, fun g hg => ?_⟩
      have hx' : x ∉ A := hnotA x (by
        rw [mem_closedBall_zero_iff] at hx
        linarith [not_le.1 hx])
      have hy' : (fun _ => r' : FourVec) ∉ A := hnotA _ hy₀.ge
      rw [apply_eq_zero_of_notMem hg hx', apply_eq_zero_of_notMem hg hy',
        fderiv_eq_zero_of_notMem hg hx', fderiv_eq_zero_of_notMem hg hy']
      exact ⟨rfl, rfl⟩
  obtain ⟨D, hDc, hDs, hD⟩ := exists_countable_c1_approx (isCompact_closedBall _ _) (c1SupportedIn A)
    (fun g hg => hg.1) hz
  refine ⟨D, hDc, hDs, fun f hf ε hε => ?_⟩
  obtain ⟨h, hh, hc⟩ := hD f hf ε hε
  exact ⟨h, hh, c1Bounded_sub hf.1 (hDs hh).1 hc⟩
def c1Class : AdmissibleConstants.NormedFunctionClass FourVec where
  supportedIn := c1SupportedIn
  SizeLE := C1Bounded
  supportedIn_mono h _ hf := ⟨hf.1, hf.2.trans h⟩
  sub_mem {A f h} hA hf hh := ⟨hf.1.sub hh.1, closure_minimal (fun x hx => by
    by_contra hn
    exact hx (by simp [apply_eq_zero_of_notMem hf hn, apply_eq_zero_of_notMem hh hn])) hA⟩
  sizeLE_mono h hb := h.mono hb
  sizeLE_of_sub hf hh h₁ h₂ := C1Bounded.of_sub hf.1 hh.1 h₁ h₂
  exists_sizeLE hA hf := exists_c1Bounded_of_isCompact hA hf
  exists_countable_dense hA := exists_countable_c1SupportedIn hA
theorem sharpNormR4_le {f : FourVec → ℝ} (hf : ContDiff ℝ 1 f) {b : ℝ}
    (hb : C1Bounded f b) : sharpNormR4 1 f ≤ 40 * b := by
  have hb0 := hb.nonneg
  have h1 : uniformNorm f ≤ b := ciSup_le fun x => (hb x).1
  have h2 : lipConstR4 f ≤ b :=
    csInf_le ⟨0, fun c hc => hc.1⟩ ⟨hb0, fun x y => norm_sub_le_of_c1Bounded hf hb x y⟩
  refine max_le (by linarith) (by linarith)
theorem isLipschitzFor_euclid {f : FourVec → ℝ} (hf : ContDiff ℝ 1 f) {b : ℝ}
    (hb : C1Bounded f b) : IsLipschitzFor euclidDistR4 f :=
  ⟨b, hb.nonneg, fun x y => norm_sub_le_of_c1Bounded hf hb x y⟩
section Torus
variable {ℓ : ℝ}
theorem torusProj_add (a b : FourVec) : torusProj ℓ (a + b) = torusProj ℓ a + torusProj ℓ b := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_add <;> assumption
theorem comp_torusProj_add_translate (f : Torus4 ℓ → ℝ) (k : Fin 4 → ℤ) :
    (fun z => (f ∘ torusProj ℓ) (z + latticeTranslate ℓ k)) = f ∘ torusProj ℓ := by
  funext z
  simp [Function.comp, torusProj_add_latticeTranslate]
theorem fderiv_comp_torusProj_add_translate (f : Torus4 ℓ → ℝ) (x : FourVec) (k : Fin 4 → ℤ) :
    fderiv ℝ (f ∘ torusProj ℓ) (x + latticeTranslate ℓ k) = fderiv ℝ (f ∘ torusProj ℓ) x := by
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := f ∘ torusProj ℓ) (x := x) (latticeTranslate ℓ k)
  rw [← h, comp_torusProj_add_translate]
def fundamentalCube (ℓ : ℝ) : Set FourVec := Set.pi univ fun _ => Icc 0 ℓ
theorem isCompact_fundamentalCube (ℓ : ℝ) : IsCompact (fundamentalCube ℓ) :=
  isCompact_univ_pi fun _ => isCompact_Icc
theorem exists_mem_fundamentalCube (hℓ : 0 < ℓ) (x : FourVec) :
    ∃ y ∈ fundamentalCube ℓ, ∃ k : Fin 4 → ℤ, x = y + latticeTranslate ℓ k := by
  refine ⟨fun μ => toIcoMod hℓ 0 (x μ), fun μ _ => ?_, fun μ => toIcoDiv hℓ 0 (x μ), ?_⟩
  · have := toIcoMod_mem_Ico hℓ 0 (x μ)
    simp only [zero_add] at this
    exact ⟨this.1, this.2.le⟩
  · funext μ
    have := self_sub_toIcoDiv_zsmul hℓ 0 (x μ)
    simp only [Pi.add_apply, latticeTranslate]
    rw [← this, zsmul_eq_mul]
    ring
theorem exists_c1Bounded_torus (hℓ : 0 < ℓ) {f : Torus4 ℓ → ℝ} (hf : IsC1Torus f) :
    ∃ b, C1Bounded (f ∘ torusProj ℓ) b := by
  have hf' : ContDiff ℝ 1 (f ∘ torusProj ℓ) := hf
  obtain ⟨b₁, h₁⟩ := (isCompact_fundamentalCube ℓ).exists_bound_of_continuousOn
    hf'.continuous.continuousOn
  obtain ⟨b₂, h₂⟩ := (isCompact_fundamentalCube ℓ).exists_bound_of_continuousOn
    (hf'.continuous_fderiv (by norm_num)).continuousOn
  refine ⟨max b₁ b₂, fun x => ?_⟩
  obtain ⟨y, hy, k, rfl⟩ := exists_mem_fundamentalCube hℓ x
  rw [fderiv_comp_torusProj_add_translate]
  have e : (f ∘ torusProj ℓ) (y + latticeTranslate ℓ k) = (f ∘ torusProj ℓ) y :=
    congrFun (comp_torusProj_add_translate f k) y
  rw [e]
  exact ⟨(h₁ y hy).trans (le_max_left _ _), (h₂ y hy).trans (le_max_right _ _)⟩
def torusC1SupportedIn (A : Set (Torus4 ℓ)) : Set (Torus4 ℓ → ℝ) :=
  {f | IsC1Torus f ∧ tsupport f ⊆ A}
theorem comp_liftPoint (f : Torus4 ℓ → ℝ) : (f ∘ torusProj ℓ) ∘ liftPoint = f := by
  funext x
  simp [Function.comp, torusProj_liftPoint]
theorem exists_countable_torusC1SupportedIn (hℓ : 0 < ℓ) (A : Set (Torus4 ℓ)) :
    ∃ D : Set (Torus4 ℓ → ℝ), D.Countable ∧ D ⊆ torusC1SupportedIn A ∧
      ∀ f ∈ torusC1SupportedIn A, ∀ ε : ℝ, 0 < ε → ∃ h ∈ D,
        C1Bounded ((f - h) ∘ torusProj ℓ) ε := by
  obtain ⟨D, hDc, hDs, hD⟩ := exists_countable_c1_approx (isCompact_fundamentalCube ℓ)
    ((fun f : Torus4 ℓ → ℝ => f ∘ torusProj ℓ) '' torusC1SupportedIn A)
    (by
      rintro _ ⟨f, hf, rfl⟩
      exact hf.1)
    (by
      intro x
      obtain ⟨y, hy, k, rfl⟩ := exists_mem_fundamentalCube hℓ x
      refine ⟨y, hy, ?_⟩
      rintro _ ⟨f, -, rfl⟩
      exact ⟨congrFun (comp_torusProj_add_translate f k) y, fderiv_comp_torusProj_add_translate f y k⟩)
  refine ⟨(fun g => g ∘ liftPoint) '' D, hDc.image _, ?_, fun f hf ε hε => ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨f, hf, rfl⟩ := hDs hg
    simpa only [comp_liftPoint] using hf
  · obtain ⟨g, hg, hc⟩ := hD _ ⟨f, hf, rfl⟩ ε hε
    obtain ⟨f', hf', rfl⟩ := hDs hg
    refine ⟨f', ⟨_, hg, comp_liftPoint f'⟩, ?_⟩
    exact c1Bounded_sub (f := f ∘ torusProj ℓ) (h := f' ∘ torusProj ℓ) hf.1 hf'.1 hc
def torusC1Class (hℓ : 0 < ℓ) : AdmissibleConstants.NormedFunctionClass (Torus4 ℓ) where
  supportedIn := torusC1SupportedIn
  SizeLE f b := C1Bounded (f ∘ torusProj ℓ) b
  supportedIn_mono h _ hf := ⟨hf.1, hf.2.trans h⟩
  sub_mem {A f h} hA hf hh := ⟨ContDiff.sub (f := f ∘ torusProj ℓ) (g := h ∘ torusProj ℓ) hf.1 hh.1,
    closure_minimal (fun x hx => by
      by_contra hn
      have h₁ : f x = 0 := image_eq_zero_of_notMem_tsupport fun h => hn (hf.2 h)
      have h₂ : h x = 0 := image_eq_zero_of_notMem_tsupport fun h' => hn (hh.2 h')
      exact hx (by simp [h₁, h₂])) hA⟩
  sizeLE_mono h hb := h.mono hb
  sizeLE_of_sub {A f h b ε} hf hh h₁ h₂ := C1Bounded.of_sub (f := f ∘ torusProj ℓ)
    (h := h ∘ torusProj ℓ) hf.1 hh.1 h₁ h₂
  exists_sizeLE _ hf := exists_c1Bounded_torus hℓ hf.1
  exists_countable_dense {A} _ := exists_countable_torusC1SupportedIn hℓ A
theorem norm_sub_le_torus {f : Torus4 ℓ → ℝ} (hf : IsC1Torus f) {b : ℝ}
    (hb : C1Bounded (f ∘ torusProj ℓ) b) (x y : Torus4 ℓ) :
    ‖f x - f y‖ ≤ b * euclidDistTorus x y := by
  have hf' : ContDiff ℝ 1 (f ∘ torusProj ℓ) := hf
  have hb0 := hb.nonneg
  have key : ∀ w : FourVec, torusProj ℓ w = x - y → ‖f x - f y‖ ≤ b * euclidNormVec w := by
    intro w hw
    have hx : torusProj ℓ (liftPoint y + w) = x := by
      rw [torusProj_add, torusProj_liftPoint, hw]
      abel
    have h := norm_sub_le_of_c1Bounded hf' hb (liftPoint y + w) (liftPoint y)
    simpa only [Function.comp, hx, torusProj_liftPoint, add_sub_cancel_left] using h
  obtain ⟨w₀, hw₀⟩ := torusProj_surjective ℓ (x - y)
  rcases hb0.eq_or_lt with h0 | h0
  · have := key w₀ hw₀
    rw [← h0, zero_mul] at this
    rw [← h0, zero_mul]
    exact this
  · have hle : ‖f x - f y‖ / b ≤ torusEuclidNorm (x - y) := by
      refine le_csInf ⟨_, w₀, hw₀, rfl⟩ ?_
      rintro _ ⟨w, hw, rfl⟩
      rw [div_le_iff₀' h0]
      exact key w hw
    rw [div_le_iff₀' h0] at hle
    exact hle
theorem isLipschitzFor_torus {f : Torus4 ℓ → ℝ} (hf : IsC1Torus f) {b : ℝ}
    (hb : C1Bounded (f ∘ torusProj ℓ) b) : IsLipschitzFor euclidDistTorus f :=
  ⟨b, hb.nonneg, fun x y => norm_sub_le_torus hf hb x y⟩
theorem sharpNormTorus_nonneg (M : ℝ) (f : Torus4 ℓ → ℝ) : 0 ≤ sharpNormTorus M f :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem sharpNormTorus_le {f : Torus4 ℓ → ℝ} (hf : IsC1Torus f) {b : ℝ}
    (hb : C1Bounded (f ∘ torusProj ℓ) b) : sharpNormTorus 1 f ≤ 40 * b := by
  have hb0 := hb.nonneg
  have h1 : uniformNorm f ≤ b := ciSup_le fun x => by
    have := (hb (liftPoint x)).1
    simpa only [Function.comp, torusProj_liftPoint, Real.norm_eq_abs] using this
  have h2 : lipConstTorus f ≤ b :=
    csInf_le ⟨0, fun c hc => hc.1⟩ ⟨hb0, fun x y => norm_sub_le_torus hf hb x y⟩
  refine max_le (by linarith) (by linarith)
theorem norm_le_torusEuclidNorm (z : Torus4 ℓ) : ‖z‖ ≤ torusEuclidNorm z := by
  obtain ⟨w₀, hw₀⟩ := torusProj_surjective ℓ z
  refine le_csInf ⟨_, w₀, hw₀, rfl⟩ ?_
  rintro _ ⟨w, hw, rfl⟩
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun μ => ?_
  have hz : z μ = (w μ : AddCircle ℓ) := (congrFun hw μ).symm
  rw [hz]
  refine (QuotientAddGroup.norm_mk_le_norm (S := _)).trans ?_
  exact (norm_le_pi_norm w μ).trans (norm_le_euclidNormVec w)
theorem torusEuclidNorm_zero_nonpos : torusEuclidNorm (0 : Torus4 ℓ) ≤ 0 := by
  refine csInf_le ⟨0, ?_⟩ ⟨0, ?_, ?_⟩
  · rintro _ ⟨w, -, rfl⟩
    exact Real.sqrt_nonneg _
  · funext μ
    simp [torusProj]
  · simp [euclidNormVec]
theorem disjoint_tsupport_of_separated {n : ℕ} {f : Fin n → Torus4 ℓ → ℝ} {d : ℝ}
    (h : HasSeparatedSupportsTorus f d) {i k : Fin n} (hik : i ≠ k) :
    Disjoint (tsupport (f i)) (tsupport (f k)) := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  have h₁ := h.2 i k hik
  have h₂ : setEuclidDist (tsupport (f i)) (tsupport (f k)) ≤
      ENNReal.ofReal (torusEuclidNorm (x - x)) :=
    iInf₂_le_of_le x hx (iInf₂_le_of_le x hx' le_rfl)
  rw [sub_self] at h₂
  have h₃ : ENNReal.ofReal (torusEuclidNorm (0 : Torus4 ℓ)) = 0 :=
    ENNReal.ofReal_of_nonpos torusEuclidNorm_zero_nonpos
  have h₄ := h₁.trans h₂
  rw [h₃] at h₄
  have := h.1
  simp at h₄
  linarith
theorem hasSeparatedSupportsTorus_of_dist {n : ℕ} {f : Fin n → Torus4 ℓ → ℝ}
    {A : Fin n → Set (Torus4 ℓ)} {d : ℝ} (hd : 0 < d) (hA : ∀ i, tsupport (f i) ⊆ A i)
    (hs : ∀ i k, i ≠ k → ∀ x ∈ A i, ∀ y ∈ A k, d ≤ dist x y) : HasSeparatedSupportsTorus f d :=
  ⟨hd, fun i k hik => le_iInf₂ fun x hx => le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal
    ((hs i k hik x (hA i hx) y (hA k hy)).trans (by
      rw [dist_eq_norm]
      exact norm_le_torusEuclidNorm _))⟩
end Torus
theorem mul_prod_le_forty_pow {n : ℕ} (C : ℝ) {s t : Fin n → ℝ} (hs : ∀ i, 0 ≤ s i)
    (hst : ∀ i, s i ≤ 40 * t i) : C * ∏ i, s i ≤ |C| * 40 ^ n * ∏ i, t i := by
  have h₁ : C * ∏ i, s i ≤ |C| * ∏ i, s i :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.prod_nonneg fun i _ => hs i)
  have h₂ : ∏ i, s i ≤ ∏ i, (40 * t i) := Finset.prod_le_prod (fun i _ => hs i) fun i _ => hst i
  have h₃ : ∏ i, (40 * t i) = 40 ^ n * ∏ i, t i := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc C * ∏ i, s i ≤ |C| * ∏ i, s i := h₁
    _ ≤ |C| * ∏ i, (40 * t i) := mul_le_mul_of_nonneg_left h₂ (abs_nonneg _)
    _ = |C| * 40 ^ n * ∏ i, t i := by rw [h₃]; ring
theorem ursell_sub_update
    (hM : TorusCumulants.Multilinearity.claim)
    {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (m K : ℕ+) {β : ℝ} (hβ : 0 < β) {n : ℕ}
    (hn : 1 ≤ n) {u : Fin n → PeriodicLattice.FourTorus L m → ℝ}
    (hu : ∀ i, IsLipschitzFor euclidDistTorus (u i)) (i : Fin n)
    {v : PeriodicLattice.FourTorus L m → ℝ} (hv : IsLipschitzFor euclidDistTorus v) :
    PeriodicLattice.torusUrsellFunction L m K β u -
        PeriodicLattice.torusUrsellFunction L m K β (Function.update u i v) =
      PeriodicLattice.torusUrsellFunction L m K β (Function.update u i (u i - v)) := by
  have h₃ := (hM.2 ⟨L, hL, K, m⟩ β n hβ hn).2.2.1
  have h₄ := (h₃ u hu).2 i (u i) v 1 (-1) (hu i) hv
  have e : (fun x => (1 : ℝ) * u i x + (-1) * v x) = u i - v := by
    funext x
    simp [sub_eq_add_neg]
  rw [e, Function.update_eq_self] at h₄
  have h₅ : PeriodicLattice.torusUrsellFunction L m K β (Function.update u i (u i - v)) =
      ((1 : ℝ) : ℂ) * PeriodicLattice.torusUrsellFunction L m K β u +
        ((-1 : ℝ) : ℂ) * PeriodicLattice.torusUrsellFunction L m K β (Function.update u i v) := h₄
  rw [h₅]
  push_cast
  ring
theorem torusSide_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (m : ℕ) :
    0 < PeriodicLattice.torusSide L m := by
  have h : (0 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 0 < L)
  unfold PeriodicLattice.torusSide
  positivity
theorem exists_subseq_tendsto_fixedTorus (hA : AdmissibleConstants.DiagonalSubsequenceExists)
    (hM : TorusCumulants.Multilinearity.claim)
    {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (m : ℕ+) (K : ℕ → ℕ+) (β : ℕ → ℝ)
    (hβ : ∀ j, 0 < β j) {Ab bb : ℝ} (hb : ∀ j, AdmissibleConstants.TorusClusterBound L 1 (K j) (β j) Ab bb) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, 2 ≤ n → ∀ X : Fin n → PeriodicLattice.FourTorus L m → ℝ,
      (∀ i, IsC1Torus (X i)) → (∃ d : ℝ, 0 < d ∧ HasSeparatedSupportsTorus X d) →
      ∃ z : ℂ, Tendsto (fun i => PeriodicLattice.torusUrsellFunction L m (K (φ i)) (β (φ i)) X)
        atTop (𝓝 z) := by
  have hℓ := torusSide_pos hL m
  have : Fact (0 < PeriodicLattice.torusSide L m) := ⟨hℓ⟩
  have lip : ∀ f : PeriodicLattice.FourTorus L m → ℝ, IsC1Torus f → IsLipschitzFor euclidDistTorus f :=
    fun f hf => let ⟨_, hb'⟩ := exists_c1Bounded_torus hℓ hf; isLipschitzFor_torus hf hb'
  obtain ⟨φ, hφ, hlim⟩ := hA (Torus4 (PeriodicLattice.torusSide L m)) (torusC1Class hℓ)
    (fun n => {X | (∀ i, IsC1Torus (X i)) ∧ ∃ d : ℝ, 0 < d ∧ HasSeparatedSupportsTorus X d})
    (fun j n X => PeriodicLattice.torusUrsellFunction L m (K j) (β j) X)
    (by
      intro n X hX
      refine ⟨fun i => (isClosed_tsupport _).isCompact, fun i => ⟨hX.1 i, subset_rfl⟩,
        fun i k hik => ?_⟩
      obtain ⟨d, -, hd⟩ := hX.2
      exact disjoint_tsupport_of_separated hd hik)
    (by
      intro n hn A hAc d hd hs
      refine ⟨|AdmissibleConstants.cumulantBound L Ab bb n d (PeriodicLattice.torusSide L m)| * 40 ^ n,
        0, by positivity, fun j _ => ⟨?_, ?_⟩⟩
      · intro u hu i v hv
        have hu' : ∀ l, u l ∈ torusC1SupportedIn (A l) := hu
        have hv' : v ∈ torusC1SupportedIn (A i) := hv
        exact ursell_sub_update hM hL m (K j) (hβ j) (by omega) (fun l => lip _ (hu' l).1) i
          (lip _ hv'.1)
      · intro u hu bnd hbnd
        have hu' : ∀ l, u l ∈ torusC1SupportedIn (A l) := hu
        refine (hb j m n hn d hd u (fun l => lip _ (hu' l).1)
          (hasSeparatedSupportsTorus_of_dist hd (fun l => (hu' l).2) hs)).trans ?_
        exact mul_prod_le_forty_pow _ (fun l => sharpNormTorus_nonneg _ _)
          fun l => sharpNormTorus_le (hu' l).1 (hbnd l))
  exact ⟨φ, hφ, fun n hn X h₁ h₂ => hlim n hn X ⟨h₁, h₂⟩⟩
theorem eventually_le_torusSide {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) {m : ℕ → ℕ+}
    (hm : Tendsto m atTop atTop) (B : ℝ) : ∀ᶠ j in atTop, B ≤ PeriodicLattice.torusSide L (m j) := by
  filter_upwards [hm.eventually_ge_atTop (Nat.succPNat ⌈B⌉₊)] with j hj
  have h₁ : ⌈B⌉₊ + 1 ≤ (m j : ℕ) := hj
  have h₂ : (m j : ℕ) < L ^ (m j : ℕ) := Nat.lt_pow_self (by have := hL.2; omega)
  have h₃ : (⌈B⌉₊ : ℝ) ≤ (L : ℝ) ^ (m j : ℕ) := by
    exact_mod_cast (by omega : ⌈B⌉₊ ≤ L ^ (m j : ℕ))
  have h₄ := Nat.le_ceil B
  unfold PeriodicLattice.torusSide
  linarith
theorem periodize_properties (hTr : LipschitzPeriodization.Statement)
    {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (m : ℕ+) {ρ : ℝ} (hρ : 0 < ρ)
    (hside : 4 * (ρ + 1) ≤ PeriodicLattice.torusSide L m) {f h : FourVec → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : IsCompact (tsupport f)) (hfb : ∀ x ∈ tsupport f, euclidNormVec x < ρ)
    (hh : ContDiff ℝ 1 h) (hhc : IsCompact (tsupport h)) (hhb : ∀ x ∈ tsupport h, euclidNormVec x < ρ) :
    IsLipschitzFor euclidDistTorus (periodize (PeriodicLattice.torusSide L m) f) ∧
      sharpNormTorus 1 (periodize (PeriodicLattice.torusSide L m) f) = sharpNormR4 1 f ∧
      periodize (PeriodicLattice.torusSide L m) (f - h) =
        periodize (PeriodicLattice.torusSide L m) f - periodize (PeriodicLattice.torusSide L m) h ∧
      tsupport (periodize (PeriodicLattice.torusSide L m) f) ⊆
        closedBallTorus (torusProj (PeriodicLattice.torusSide L m) 0) ρ ∧
      setEuclidDist (tsupport (periodize (PeriodicLattice.torusSide L m) f))
        (tsupport (periodize (PeriodicLattice.torusSide L m) h)) =
        setDistR4 (tsupport f) (tsupport h) := by
  obtain ⟨bf, hbf⟩ := exists_c1Bounded_of_isCompact hfc ⟨hf, subset_rfl⟩
  obtain ⟨bh, hbh⟩ := exists_c1Bounded_of_isCompact hhc ⟨hh, subset_rfl⟩
  let c : ExpandingTori.PeriodizationMargin L := ⟨1, one_pos, by
    have : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
    linarith⟩
  let D : Conventions.StandingParameters := ⟨L, hL, 1, m⟩
  have hr : ρ ≤ c.radius D.side := by
    show ρ ≤ PeriodicLattice.torusSide L m / 4 - 1
    linarith
  obtain ⟨-, -, hlin, -, hnorm, -, hsup, -⟩ := hTr D c ρ f h hρ hr (isLipschitzFor_euclid hf hbf)
    (isLipschitzFor_euclid hh hbh) ⟨hfc, hfb⟩ ⟨hhc, hhb⟩
  have e : (1 : ℝ) • f + (-1 : ℝ) • h = f - h := by
    funext x
    simp [sub_eq_add_neg]
  have hT : periodize (PeriodicLattice.torusSide L m) (f - h) =
      periodize (PeriodicLattice.torusSide L m) f - periodize (PeriodicLattice.torusSide L m) h := by
    have h₁ := (hlin 1 (-1)).2
    rw [e] at h₁
    refine h₁.trans ?_
    funext x
    simp [sub_eq_add_neg]
    rfl
  have hs₁ : tsupport (periodize (PeriodicLattice.torusSide L m) f) =
      torusProj (PeriodicLattice.torusSide L m) '' tsupport f := hsup.1
  refine ⟨hnorm.2.2.1, hnorm.2.2.2.2 1, hT, ?_, hsup.2.2⟩
  rw [hs₁]
  rintro _ ⟨z, hz, rfl⟩
  have e₀ : torusProj (PeriodicLattice.torusSide L m) z - torusProj (PeriodicLattice.torusSide L m) 0 =
      torusProj (PeriodicLattice.torusSide L m) z := by
    funext μ
    simp [torusProj]
  show torusEuclidNorm (torusProj (PeriodicLattice.torusSide L m) z -
    torusProj (PeriodicLattice.torusSide L m) 0) ≤ ρ
  rw [e₀]
  have hmem : euclidNormVec z ∈ euclidNormVec ''
      (torusProj (PeriodicLattice.torusSide L m) ⁻¹' {torusProj (PeriodicLattice.torusSide L m) z}) :=
    ⟨z, rfl, rfl⟩
  have hle : torusEuclidNorm (torusProj (PeriodicLattice.torusSide L m) z) ≤ euclidNormVec z :=
    csInf_le ⟨0, by
      rintro _ ⟨w, -, rfl⟩
      exact Real.sqrt_nonneg _⟩ hmem
  exact hle.trans (hfb z hz).le
theorem comp_update {n : ℕ} {α γ : Type*} (T : α → γ) (u : Fin n → α) (i : Fin n) (v : α) :
    (fun l => T (Function.update u i v l)) = Function.update (fun l => T (u l)) i (T v) := by
  funext l
  by_cases hl : l = i
  · subst hl
    simp
  · simp [Function.update_of_ne hl]
theorem exists_subseq_tendsto_periodize (hA : AdmissibleConstants.DiagonalSubsequenceExists)
    (hM : TorusCumulants.Multilinearity.claim)
    (hTr : LipschitzPeriodization.Statement)
    {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (m K : ℕ → ℕ+) (β : ℕ → ℝ)
    (hβ : ∀ j, 0 < β j) {Ab bb : ℝ}
    (hb : ∀ j, AdmissibleConstants.BallClusterBoundOnTori L 1 (K j) (β j) Ab bb)
    (hm : Tendsto m atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, 2 ≤ n → ∀ X : TestSpaces.SepTupleOfCard n, ∃ z : ℂ,
      Tendsto (fun i => PeriodicLattice.torusUrsellFunction L (m (φ i)) (K (φ i)) (β (φ i))
        (fun l => periodize (PeriodicLattice.torusSide L (m (φ i))) (X.1 l))) atTop (𝓝 z) := by
  obtain ⟨φ, hφ, hlim⟩ := hA FourVec c1Class
    (fun n => TestSpaces.disjointSupportTuples (univ : Set FourVec) n)
    (fun j n X => PeriodicLattice.torusUrsellFunction L (m j) (K j) (β j)
      (fun l => periodize (PeriodicLattice.torusSide L (m j)) (X l)))
    (by
      intro n X hX
      exact ⟨fun i => (hX.1 i).2.1, fun i => ⟨(hX.1 i).1, subset_rfl⟩, hX.2⟩)
    (by
      intro n hn A hAc d hd hs
      have hU : IsCompact (⋃ i, A i) := isCompact_iUnion hAc
      obtain ⟨r, hr⟩ := hU.isBounded.subset_closedBall (0 : FourVec)
      set ρ : ℝ := 2 * (|r| + 1) with hρdef
      have hρ : 0 < ρ := by positivity
      have hin : ∀ i, ∀ x ∈ A i, euclidNormVec x < ρ := by
        intro i x hx
        have h₁ := hr (mem_iUnion.2 ⟨i, hx⟩)
        rw [mem_closedBall_zero_iff] at h₁
        have h₂ := euclidNormVec_le_two_mul_norm x
        have h₃ := le_abs_self r
        linarith
      obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_le_torusSide hL hm (4 * (ρ + 1)))
      refine ⟨|AdmissibleConstants.cumulantBound L Ab bb n d ρ| * 40 ^ n, N, by positivity,
        fun j hj => ?_⟩
      have hfacts : ∀ {a a' : Fin n} {f h : FourVec → ℝ}, f ∈ c1SupportedIn (A a) →
          h ∈ c1SupportedIn (A a') → _ := fun {a a' f h} hf hh =>
        periodize_properties hTr hL (m j) hρ (hN j hj) hf.1
          ((hAc a).of_isClosed_subset (isClosed_tsupport _) hf.2) (fun x hx => hin a x (hf.2 hx))
          hh.1 ((hAc a').of_isClosed_subset (isClosed_tsupport _) hh.2)
          (fun x hx => hin a' x (hh.2 hx))
      constructor
      · intro u hu i v hv
        have hu' : ∀ l, u l ∈ c1SupportedIn (A l) := hu
        have hv' : v ∈ c1SupportedIn (A i) := hv
        have h := ursell_sub_update hM hL (m j) (K j) (hβ j) (by omega)
          (u := fun l => periodize (PeriodicLattice.torusSide L (m j)) (u l))
          (fun l => (hfacts (hu' l) (hu' l)).1) i
          (v := periodize (PeriodicLattice.torusSide L (m j)) v) (hfacts hv' hv').1
        show PeriodicLattice.torusUrsellFunction L (m j) (K j) (β j)
              (fun l => periodize (PeriodicLattice.torusSide L (m j)) (u l)) -
            PeriodicLattice.torusUrsellFunction L (m j) (K j) (β j)
              (fun l => periodize (PeriodicLattice.torusSide L (m j)) (Function.update u i v l)) =
          PeriodicLattice.torusUrsellFunction L (m j) (K j) (β j)
              (fun l => periodize (PeriodicLattice.torusSide L (m j)) (Function.update u i (u i - v) l))
        rw [comp_update, comp_update, (hfacts (hu' i) hv').2.2.1]
        exact h
      · intro u hu bnd hbnd
        have hu' : ∀ l, u l ∈ c1SupportedIn (A l) := hu
        have hsep : HasSeparatedSupportsTorus
            (fun l => periodize (PeriodicLattice.torusSide L (m j)) (u l)) d := by
          refine ⟨hd, fun i k hik => ?_⟩
          show ENNReal.ofReal d ≤ setEuclidDist
            (tsupport (periodize (PeriodicLattice.torusSide L (m j)) (u i)))
            (tsupport (periodize (PeriodicLattice.torusSide L (m j)) (u k)))
          rw [(hfacts (hu' i) (hu' k)).2.2.2.2]
          refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal ?_
          refine (hs i k hik x ((hu' i).2 hx) y ((hu' k).2 hy)).trans ?_
          rw [dist_eq_norm]
          exact norm_le_euclidNormVec _
        refine (hb j (m j) n hn ρ d hρ hd _ (fun l => (hfacts (hu' l) (hu' l)).1)
          (fun l => ⟨_, (hfacts (hu' l) (hu' l)).2.2.2.1⟩) hsep).trans ?_
        refine mul_prod_le_forty_pow _ (fun l => sharpNormTorus_nonneg _ _) fun l => ?_
        rw [(hfacts (hu' l) (hu' l)).2.1]
        exact sharpNormR4_le (hu' l).1 (hbnd l))
  exact ⟨φ, hφ, fun n hn X => hlim n hn X.1 X.2⟩
theorem natPred_tendsto_atTop : Tendsto PNat.natPred atTop atTop :=
  tendsto_atTop.2 fun b => by
    filter_upwards [eventually_ge_atTop (Nat.succPNat b)] with i hi
    have : b + 1 ≤ (i : ℕ) := hi
    have h := PNat.natPred_add_one i
    omega
theorem succPNat_tendsto_atTop : Tendsto Nat.succPNat atTop atTop :=
  tendsto_atTop.2 fun b => by
    filter_upwards [eventually_ge_atTop (b : ℕ)] with i hi
    show (b : ℕ) ≤ i + 1
    omega
theorem strictMono_succPNat_comp {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    StrictMono fun i : ℕ+ => (φ i.natPred).succPNat := by
  intro i i' h
  refine Nat.succPNat_lt_succPNat.2 (hφ ?_)
  have h₁ := PNat.natPred_add_one i
  have h₂ := PNat.natPred_add_one i'
  have h₃ : (i : ℕ) < i' := h
  omega
open TrajectoryData in
theorem subsequentialLimitsAlongFlow_holds
    (hF : SystemOfAdmissibleConstants.FamilyBoundsAlongFlow)
    (hM : TorusCumulants.Multilinearity.claim)
    (hTr : LipschitzPeriodization.Statement)
    (hA : AdmissibleConstants.DiagonalSubsequenceExists) :
    SystemOfAdmissibleConstants.SubsequentialLimitsAlongParameterSequence := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, H⟩ := hF a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hoddL hL₀ T hTa hTL hDr hcs hon hr hC => ?_⟩
  obtain ⟨y₀, Hy⟩ := H L hoddL hL₀ T hTa hTL hDr hcs hon hr hC
  refine ⟨y₀, fun y hy hrow hwil D hD g hg hfl => ?_⟩
  obtain ⟨Ab, bb, -, -, hcl, -⟩ := Hy y hy hrow hwil D hD g hg hfl
  have hL : Conventions.IsAdmissibleBlockingFactor T.side :=
    ⟨hDr.L_odd, le_trans (by norm_num : (13 : ℕ) ≤ 2 ^ 40) hDr.L_ge⟩
  have hβpos : ∀ {K : ℕ} {β : ℝ}, β ∈ D.passageWindow K g → 0 < β := by
    intro K β hβ
    have h₁ : g ^ (-2 : ℤ) + D.shift ≤ β := hβ.1
    have h₂ : 0 < g ^ (-2 : ℤ) := zpow_pos hg _
    have h₃ : 0 < T.B := hD.errorMargin.admissible.B_pos
    have h₄ := hD.shift_ge
    linarith
  refine ⟨?_, ?_⟩
  · intro K m β hw _ hm
    obtain ⟨φ₀, h₀, hl⟩ := exists_subseq_tendsto_periodize hA hM hTr hL (fun j => m j.succPNat)
      (fun j => K j.succPNat) (fun j => β j.succPNat) (fun j => hβpos (hw _))
      (fun j => (hcl 1 le_rfl).ballOnTori _ _ (hw _)) (hm.comp succPNat_tendsto_atTop)
    refine ⟨fun i => (φ₀ i.natPred).succPNat, strictMono_succPNat_comp h₀, fun n hn X => ?_⟩
    obtain ⟨z, hz⟩ := hl n hn X
    exact ⟨z, hz.comp natPred_tendsto_atTop⟩
  · intro m K β hw _
    obtain ⟨φ₀, h₀, hl⟩ := exists_subseq_tendsto_fixedTorus hA hM hL m (fun j => K j.succPNat)
      (fun j => β j.succPNat) (fun j => hβpos (hw _))
      (fun j => (hcl 1 le_rfl).torus _ _ (hw _))
    refine ⟨fun i => (φ₀ i.natPred).succPNat, strictMono_succPNat_comp h₀, fun n hn X h₁ h₂ => ?_⟩
    obtain ⟨z, hz⟩ := hl n hn X h₁ h₂
    exact ⟨z, hz.comp natPred_tendsto_atTop⟩
end SystemOfAdmissibleConstants.TrajectoryLimits
end YangMills.Construction
end
