import YangMills.Construction.Matrices.CalculusOfHolomorphicMapsProof
import YangMills.Construction.RotationInvariance.DensityOfThePlateFunctionsAtDistinctPointsProof
import YangMills.Construction.Analysis.ZerosOfAnalyticMapsAndThinSets
import YangMills.Construction.RotationInvariance.DeterminationOfHolomorphicFunctionsOfTheDifferencesProof
import YangMills.Construction.RotationInvariance.TopFrequencyRangeSumsAndRate
import Mathlib
set_option autoImplicit false
open Complex (I)
open YangMills.Construction.RealPlane YangMills.Construction.ForwardTube
open YangMills.Construction.Coordinates
open Filter Topology
open YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus (scalarEquiv)
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.DistinctHarmonics
variable {q : ℕ}
theorem rotate_apply_zero (t : ℝ) (y : RealPlane) :
    rotate t y 0 = y 0 * Real.cos t - y 1 * Real.sin t := by
  simp [RealPlane.rotate]
theorem rotate_apply_one (t : ℝ) (y : RealPlane) :
    rotate t y 1 = y 0 * Real.sin t + y 1 * Real.cos t := by
  simp [RealPlane.rotate]
theorem rotate_zero (y : RealPlane) : rotate 0 y = y := by apply _root_.YangMills.Construction.EuclideanFunctionals.ProductMotions.rotate_zero <;> assumption
theorem rotate_rotate (a b : ℝ) (y : RealPlane) :
    rotate a (rotate b y) = rotate (a + b) y := by apply _root_.YangMills.Construction.EuclideanFunctionals.ProductMotions.rotate_rotate <;> assumption
theorem rotate_add (t : ℝ) (y u : RealPlane) :
    rotate t (y + u) = rotate t y + rotate t u := by
  ext i
  fin_cases i <;> simp [RealPlane.rotate] <;> ring
theorem rotate_injective (t : ℝ) : Function.Injective (rotate t) := by
  intro y y' e
  have h := congrArg (rotate (-t)) e
  simpa [rotate_rotate, rotate_zero] using h
theorem exists_angle_injective_fst {n : ℕ} {y : Fin n → RealPlane}
    (hy : Function.Injective y) :
    ∃ t : ℝ, Function.Injective fun i => mapPoints (rotate t) y i 0 := by
  classical
  let B : Fin n × Fin n → Set ℝ := fun p =>
    if p.1 = p.2 then ∅ else {s | (y p.1 0 - y p.2 0) - s * (y p.1 1 - y p.2 1) = 0}
  have hB : ∀ p, (B p).Finite := by
    intro p
    by_cases hp : p.1 = p.2
    · simp [B, hp]
    · simp only [B, if_neg hp]
      apply Set.Subsingleton.finite
      intro s hs s' hs'
      have hne : y p.1 ≠ y p.2 := fun e => hp (hy e)
      simp only [Set.mem_setOf_eq] at hs hs'
      by_cases hb : y p.1 1 - y p.2 1 = 0
      · exfalso
        apply hne
        have ha : y p.1 0 - y p.2 0 = 0 := by
          rw [hb, mul_zero, sub_zero] at hs
          exact hs
        ext i
        fin_cases i
        · simpa using sub_eq_zero.mp ha
        · simpa using sub_eq_zero.mp hb
      · have hz : (s - s') * (y p.1 1 - y p.2 1) = 0 := by linear_combination hs' - hs
        rcases mul_eq_zero.mp hz with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hb
  have hfin : (⋃ p, B p).Finite := Set.finite_iUnion hB
  obtain ⟨s, hs⟩ := hfin.infinite_compl.nonempty
  refine ⟨Real.arctan s, ?_⟩
  intro i j hij
  by_contra hne
  apply hs
  refine Set.mem_iUnion.mpr ⟨(i, j), ?_⟩
  simp only [B, if_neg hne, Set.mem_setOf_eq]
  have hc : Real.cos (Real.arctan s) ≠ 0 := (Real.cos_arctan_pos s).ne'
  have hsin : Real.sin (Real.arctan s) = s * Real.cos (Real.arctan s) := by
    have h1 : Real.sin (Real.arctan s) / Real.cos (Real.arctan s) = s := by
      rw [← Real.tan_eq_sin_div_cos, Real.tan_arctan]
    rw [div_eq_iff hc] at h1
    exact h1
  simp only [mapPoints, rotate_apply_zero] at hij
  rw [hsin] at hij
  have hz : Real.cos (Real.arctan s) * ((y i 0 - y j 0) - s * (y i 1 - y j 1)) = 0 := by
    linear_combination hij
  exact (mul_eq_zero.mp hz).resolve_left hc
theorem isOpen_injectivePointTuples (n : ℕ) : IsOpen (injectivePointTuples n) := by
  have he : injectivePointTuples n = ⋂ (i : Fin n) (j : Fin n) (_ : i ≠ j), {y | y i ≠ y j} := by
    ext y
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun hy i j hij e => hij (hy e), fun hy i j e => by_contra fun hij => hy i j hij e⟩
  rw [he]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun _ => ?_
  exact isOpen_ne_fun (continuous_apply i) (continuous_apply j)
theorem scalarEquiv_apply (x : ℂ) (j : Fin 1) : scalarEquiv x j = x := by apply _root_.YangMills.DeltaSharedProofs.p23888 <;> assumption
theorem finProd_cases {p : ℕ} (k : Fin (p * 2)) :
    ∃ i : Fin p, k = finProdFinEquiv (i, 0) ∨ k = finProdFinEquiv (i, 1) := by apply _root_.YangMills.Construction.EuclideanFunctionals.HarmonicDensity.exists_finProdFinEquiv_eq <;> assumption
def pairTupleLinearEquiv (p : ℕ) : (Fin p → ℂ × ℂ) ≃ₗ[ℂ] ComplexCoordinates (p * 2) :=
  { pairTupleEquiv p with
    map_add' := by
      intro v w
      funext k
      show pairTupleEquiv p (v + w) k = pairTupleEquiv p v k + pairTupleEquiv p w k
      obtain ⟨i, rfl | rfl⟩ := finProd_cases k
      · simp only [pairTupleEquiv_apply_fst]
        rfl
      · simp only [pairTupleEquiv_apply_snd]
        rfl
    map_smul' := by
      intro c v
      funext k
      show pairTupleEquiv p (c • v) k = c * pairTupleEquiv p v k
      obtain ⟨i, rfl | rfl⟩ := finProd_cases k
      · simp only [pairTupleEquiv_apply_fst]
        rfl
      · simp only [pairTupleEquiv_apply_snd]
        rfl }
theorem continuous_pairTupleEquiv (p : ℕ) : Continuous (pairTupleEquiv p) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TwoPointTopFrequency.continuous_pairTupleEquiv <;> assumption
theorem continuous_pairTupleEquiv_symm (p : ℕ) : Continuous (pairTupleEquiv p).symm :=
  LinearMap.continuous_of_finiteDimensional (pairTupleLinearEquiv p).symm.toLinearMap
theorem continuous_vecRe : Continuous vecRe := by
  unfold vecRe
  first
    | fun_prop
    | (refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp (continuous_pi ?_)
       intro i
       fin_cases i
       · simpa using Complex.continuous_re.comp continuous_fst
       · simpa using Complex.continuous_re.comp continuous_snd)
theorem continuous_tupleRe (p : ℕ) :
    Continuous (tupleRe : (Fin p → ℂ × ℂ) → Fin p → RealPlane) :=
  continuous_pi fun i => continuous_vecRe.comp (continuous_apply i)
theorem continuous_embedPlane : Continuous embedPlane := by apply _root_.YangMills.Construction.ForwardTube.ProductIntegralDetermination.continuous_embedPlane <;> assumption
theorem continuous_embedPlaneTuple (p : ℕ) :
    Continuous (embedPlaneTuple : (Fin p → RealPlane) → Fin p → ℂ × ℂ) := by apply _root_.YangMills.Construction.EuclideanFunctionals.HarmonicDensity.continuous_embedPlaneTuple <;> assumption
def realTupleOf (p : ℕ) (z : ComplexCoordinates (p * 2)) : Fin p → RealPlane :=
  tupleRe ((pairTupleEquiv p).symm z)
theorem continuous_realTupleOf (p : ℕ) : Continuous (realTupleOf p) :=
  (continuous_tupleRe p).comp (continuous_pairTupleEquiv_symm p)
theorem tupleRe_embedPlaneTuple {p : ℕ} (y : Fin p → RealPlane) :
    tupleRe (embedPlaneTuple y) = y :=
  funext fun i => vecRe_embedPlane (y i)
theorem embedPlaneTuple_realTupleOf {p : ℕ} {z : ComplexCoordinates (p * 2)}
    (hz : z ∈ ComplexCoordinates.realLocus (p * 2)) :
    embedPlaneTuple (realTupleOf p z) = (pairTupleEquiv p).symm z := by
  funext i
  have h0 : ((pairTupleEquiv p).symm z i).1 = z (finProdFinEquiv (i, 0)) := by
    rw [← pairTupleEquiv_apply_fst, Equiv.apply_symm_apply]
  have h1 : ((pairTupleEquiv p).symm z i).2 = z (finProdFinEquiv (i, 1)) := by
    rw [← pairTupleEquiv_apply_snd, Equiv.apply_symm_apply]
  have i0 : ((pairTupleEquiv p).symm z i).1.im = 0 := by rw [h0]; exact hz _
  have i1 : ((pairTupleEquiv p).symm z i).2.im = 0 := by rw [h1]; exact hz _
  refine Prod.ext (Complex.ext ?_ ?_) (Complex.ext ?_ ?_)
  · simp [embedPlaneTuple, realTupleOf, tupleRe, vecRe, embedPlane]
  · simp [embedPlaneTuple, realTupleOf, tupleRe, vecRe, embedPlane, i0]
  · simp [embedPlaneTuple, realTupleOf, tupleRe, vecRe, embedPlane]
  · simp [embedPlaneTuple, realTupleOf, tupleRe, vecRe, embedPlane, i1]
theorem mem_image_embed_iff {p : ℕ} (A : Set (Fin p → RealPlane))
    (z : ComplexCoordinates (p * 2)) :
    z ∈ pairTupleEquiv p '' (embedPlaneTuple '' A) ↔
      z ∈ ComplexCoordinates.realLocus (p * 2) ∧ realTupleOf p z ∈ A := by
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · intro k
      obtain ⟨i, rfl | rfl⟩ := finProd_cases k
      · rw [pairTupleEquiv_apply_fst]
        simp [embedPlaneTuple, embedPlane]
      · rw [pairTupleEquiv_apply_snd]
        simp [embedPlaneTuple, embedPlane]
    · simpa [realTupleOf, tupleRe_embedPlaneTuple] using hy
  · rintro ⟨hz, hA⟩
    refine ⟨embedPlaneTuple (realTupleOf p z), ⟨_, hA, rfl⟩, ?_⟩
    rw [embedPlaneTuple_realTupleOf hz, Equiv.apply_symm_apply]
theorem isRelativelyOpen_image_embed {p : ℕ} {A : Set (Fin p → RealPlane)} (hA : IsOpen A) :
    Matrices.ComplexMatrix2.IsRelativelyOpen (ComplexCoordinates.realLocus (p * 2))
      (pairTupleEquiv p '' (embedPlaneTuple '' A)) := by
  refine ⟨realTupleOf p ⁻¹' A, hA.preimage (continuous_realTupleOf p), ?_⟩
  ext z
  rw [mem_image_embed_iff]
  exact and_comm
theorem mem_image_pairTupleEquiv_iff {p : ℕ} (O : Set (Fin p → ℂ × ℂ))
    (z : ComplexCoordinates (p * 2)) :
    z ∈ pairTupleEquiv p '' O ↔ (pairTupleEquiv p).symm z ∈ O := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro h
    exact ⟨_, h, by simp⟩
theorem continuousOn_of_holomorphicOnTuples {p : ℕ} {O : Set (Fin p → ℂ × ℂ)}
    {f : (Fin p → ℂ × ℂ) → ℂ} (h : HolomorphicOnTuples O f) : ContinuousOn f O := by apply _root_.YangMills.Construction.EuclideanFunctionals.HarmonicRotationCovariance.continuousOn_of_holomorphicOnTuples <;> assumption
def boostTupleLinear {ζ : ℂ} (hl : IsLinearMap ℂ (complexBoost ζ)) (p : ℕ) :
    (Fin p → ℂ × ℂ) →ₗ[ℂ] Fin p → ℂ × ℂ :=
  LinearMap.pi fun i => hl.mk' _ ∘ₗ LinearMap.proj i
structure Inputs (S : ConnFamily) (φ₀ : openingAngles) (q : ℕ) : Prop where
  ordered_eq : orderedRealTuples q =
    {y | Function.Injective (fun i => y i 0) ∨ Function.Injective (fun i => y i 1)}
  ordered_subset : orderedRealTuples q ⊆ injectivePointTuples (q + 1)
  ordered_dense : Dense (orderedRealTuples q)
  ordered_isConnected : IsConnected (orderedRealTuples q)
  ordered_perm : ∀ (ς : Equiv.Perm (Fin (q + 1))) (y : Fin (q + 1) → RealPlane),
    y ∈ orderedRealTuples q ↔ permuteTuple ς y ∈ orderedRealTuples q
  ordered_translate : ∀ (u : RealPlane) (y : Fin (q + 1) → RealPlane),
    y ∈ orderedRealTuples q ↔ translateTuple y u ∈ orderedRealTuples q
  pencil_subset : pencilSet φ₀ (q + 1) ⊆ orderedRealTuples q
  union_isOpen : IsOpen (orderedTubeUnion q)
  boost_formula : ∀ (t : ℝ) (w : ℂ × ℂ), complexBoost (t : ℂ) w =
    (w.1 * (Real.cos t : ℂ) - w.2 * (Real.sin t : ℂ),
      w.1 * (Real.sin t : ℂ) + w.2 * (Real.cos t : ℂ))
  boost_linear : ∀ ζ : ℂ, IsLinearMap ℂ (complexBoost ζ)
  linear_holomorphic : ∀ N N' : ℕ, 1 ≤ N → 1 ≤ N' →
    ∀ f : ComplexCoordinates N →ₗ[ℂ] ComplexCoordinates N',
    ComplexCoordinates.IsHolomorphicIn Set.univ f
  series : ComplexCoordinates.PowerSeriesHolomorphy.Properties
  covariant : ∀ φ : Fin (q + 1) → realLabels,
    HarmonicRotationCovariance.CovariantBetweenOrdered S φ₀ φ
  holomorphic : ∀ (φ : Fin (q + 1) → realLabels) (h : ℤ),
    HolomorphicOnTuples (orderedTubeUnion q) (indexHarmonic S φ₀ φ h)
  symmetry : ∀ φ : Fin (q + 1) → realLabels,
    TubeUnionHarmonics.SymmetryAndMultilinearity S φ₀ φ
def rotatedHarmonic (S : ConnFamily) (φ₀ : openingAngles) (φ : Fin (q + 1) → realLabels) (h : ℤ)
    (t : ℝ) (y : Fin (q + 1) → RealPlane) : ℂ :=
  Complex.exp (-(4 * I * (h : ℂ) * (t : ℂ))) *
    indexHarmonic S φ₀ φ h (embedPlaneTuple (mapPoints (rotate t) y))
variable {S : ConnFamily} {φ₀ : openingAngles}
namespace Inputs
theorem embedPlane_rotate (F : Inputs S φ₀ q) (t : ℝ) (y : RealPlane) :
    embedPlane (rotate t y) = complexBoost (t : ℂ) (embedPlane y) := by
  rw [F.boost_formula]
  simp [embedPlane, rotate_apply_zero, rotate_apply_one]
theorem embedPlaneTuple_mapPoints (F : Inputs S φ₀ q) (t : ℝ)
    (y : Fin (q + 1) → RealPlane) :
    embedPlaneTuple (mapPoints (rotate t) y) =
      complexBoostTuple (t : ℂ) (embedPlaneTuple y) :=
  funext fun i => F.embedPlane_rotate t (y i)
theorem exists_rotate_ordered (F : Inputs S φ₀ q) {y : Fin (q + 1) → RealPlane}
    (hy : y ∈ injectivePointTuples (q + 1)) :
    ∃ t : ℝ, mapPoints (rotate t) y ∈ orderedRealTuples q := by
  obtain ⟨t, ht⟩ := exists_angle_injective_fst (y := y) hy
  refine ⟨t, ?_⟩
  rw [F.ordered_eq]
  exact Or.inl ht
theorem injective_of_rotate_ordered (F : Inputs S φ₀ q) {y : Fin (q + 1) → RealPlane} {t : ℝ}
    (ht : mapPoints (rotate t) y ∈ orderedRealTuples q) :
    y ∈ injectivePointTuples (q + 1) := by
  have hinj : Function.Injective (mapPoints (rotate t) y) := F.ordered_subset ht
  exact fun i j e => hinj (congrArg (rotate t) e)
theorem rotatedHarmonic_indep (F : Inputs S φ₀ q) (φ : Fin (q + 1) → realLabels) (h : ℤ)
    {y : Fin (q + 1) → RealPlane} {t t' : ℝ}
    (ht : mapPoints (rotate t) y ∈ orderedRealTuples q)
    (ht' : mapPoints (rotate t') y ∈ orderedRealTuples q) :
    rotatedHarmonic S φ₀ φ h t y = rotatedHarmonic S φ₀ φ h t' y := by
  have hrot : mapPoints (rotate (t' - t)) (mapPoints (rotate t) y) =
      mapPoints (rotate t') y := by
    funext i
    simp [mapPoints, rotate_rotate]
  have hc := F.covariant φ _ ht (t' - t) (by rw [hrot]; exact ht') h
  rw [hrot] at hc
  simp only [rotatedHarmonic]
  rw [hc, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring
theorem isRealAnalytic_of_rotated (F : Inputs S φ₀ q) {φ : Fin (q + 1) → realLabels}
    {h : ℤ} {f : (Fin (q + 1) → RealPlane) → ℂ}
    (hf : ∀ (y : Fin (q + 1) → RealPlane) (t : ℝ),
      mapPoints (rotate t) y ∈ orderedRealTuples q → f y = rotatedHarmonic S φ₀ φ h t y) :
    IsRealAnalyticTupleFun (injectivePointTuples (q + 1)) f := by
  refine ⟨isRelativelyOpen_image_embed (isOpen_injectivePointTuples _), ?_⟩
  intro a ha
  obtain ⟨har, hρ⟩ := (mem_image_embed_iff _ a).1 ha
  obtain ⟨t, ht⟩ := F.exists_rotate_ordered hρ
  have hN : 1 ≤ (q + 1) * 2 := by omega
  let L : ComplexCoordinates ((q + 1) * 2) →ₗ[ℂ] ComplexCoordinates ((q + 1) * 2) :=
    (pairTupleLinearEquiv (q + 1)).toLinearMap ∘ₗ boostTupleLinear (F.boost_linear t) (q + 1) ∘ₗ
      (pairTupleLinearEquiv (q + 1)).symm.toLinearMap
  have hL : ∀ z, (pairTupleEquiv (q + 1)).symm (L z) =
      complexBoostTuple (t : ℂ) ((pairTupleEquiv (q + 1)).symm z) :=
    fun z => (pairTupleEquiv (q + 1)).symm_apply_apply _
  let O : Set (ComplexCoordinates ((q + 1) * 2)) :=
    pairTupleEquiv (q + 1) '' orderedTubeUnion q
  let g : ComplexCoordinates ((q + 1) * 2) → ComplexCoordinates 1 :=
    scalarEquiv ∘ indexHarmonic S φ₀ φ h ∘ (pairTupleEquiv (q + 1)).symm
  have hg : ComplexCoordinates.IsHolomorphicIn O g := F.holomorphic φ h
  have hO : IsOpen O := hg.1
  have hLh := F.linear_holomorphic _ _ hN hN L
  let O' : Set (ComplexCoordinates ((q + 1) * 2)) := L ⁻¹' O
  have hO' : IsOpen O' := hO.preimage (LinearMap.continuous_of_finiteDimensional L)
  have hLh' : ComplexCoordinates.IsHolomorphicIn O' L :=
    ⟨hO', hLh.2.1.mono (Set.subset_univ _), fun b _ j => hLh.2.2 b (Set.mem_univ _) j⟩
  have h1 := ((F.series.1 _ O hO).1 1 g hg).2.2.2.1 _ O' L hLh' fun z hz => hz
  let C : ℂ := Complex.exp (-(4 * I * (h : ℂ) * (t : ℂ)))
  let Cm : ComplexCoordinates 1 →ₗ[ℂ] ComplexCoordinates 1 := C • LinearMap.id
  have hC := F.linear_holomorphic 1 1 le_rfl le_rfl Cm
  have h2 := ((F.series.1 1 Set.univ isOpen_univ).1 1 Cm hC).2.2.2.1 _ O' (g ∘ L) h1
    fun _ _ => Set.mem_univ _
  have h3 := ((F.series.1 _ O' hO').1 1 _ h2).2.2.2.2
  have hreal : ∀ {z : ComplexCoordinates ((q + 1) * 2)},
      z ∈ ComplexCoordinates.realLocus ((q + 1) * 2) →
      embedPlaneTuple (mapPoints (rotate t) (realTupleOf (q + 1) z)) =
        (pairTupleEquiv (q + 1)).symm (L z) := by
    intro z hz
    rw [F.embedPlaneTuple_mapPoints, embedPlaneTuple_realTupleOf hz, hL]
  have haO' : a ∈ O' := by
    show L a ∈ O
    rw [mem_image_pairTupleEquiv_iff, ← hreal har]
    exact ht
  obtain ⟨c, hc⟩ := h3.2 a ⟨haO', har⟩
  refine ⟨c, ?_⟩
  have hev : ∀ᶠ z in 𝓝[ComplexCoordinates.realLocus ((q + 1) * 2)] a, z ∈ O' :=
    mem_nhdsWithin_of_mem_nhds (hO'.mem_nhds haO')
  have hre : ∀ᶠ z in 𝓝[ComplexCoordinates.realLocus ((q + 1) * 2)] a,
      z ∈ ComplexCoordinates.realLocus ((q + 1) * 2) := self_mem_nhdsWithin
  filter_upwards [hc, hev, hre] with z hz hzO hzr
  have hord : mapPoints (rotate t) (realTupleOf (q + 1) z) ∈ orderedRealTuples q := by
    show embedPlaneTuple (mapPoints (rotate t) (realTupleOf (q + 1) z)) ∈ orderedTubeUnion q
    rw [hreal hzr]
    exact (mem_image_pairTupleEquiv_iff _ _).1 hzO
  have hval : scalarEquiv (f (realTupleOf (q + 1) z)) = (Cm ∘ g ∘ L) z := by
    rw [hf _ t hord]
    funext j
    simp only [rotatedHarmonic]
    rw [hreal hzr]
    show scalarEquiv (C * _) j = C * scalarEquiv _ j
    rw [scalarEquiv_apply, scalarEquiv_apply]
    rfl
  show HasSum _ (scalarEquiv (f (realTupleOf (q + 1) z)))
  rw [hval]
  exact hz
theorem continuousOn_of_rotated (F : Inputs S φ₀ q) {φ : Fin (q + 1) → realLabels}
    {h : ℤ} {f : (Fin (q + 1) → RealPlane) → ℂ}
    (hf : ∀ (y : Fin (q + 1) → RealPlane) (t : ℝ),
      mapPoints (rotate t) y ∈ orderedRealTuples q → f y = rotatedHarmonic S φ₀ φ h t y) :
    ContinuousOn f (injectivePointTuples (q + 1)) := by
  intro y hy
  obtain ⟨t, ht⟩ := F.exists_rotate_ordered hy
  let R : (Fin (q + 1) → RealPlane) → Fin (q + 1) → ℂ × ℂ :=
    fun y' => complexBoostTuple (t : ℂ) (embedPlaneTuple y')
  have hRc : Continuous R :=
    (LinearMap.continuous_of_finiteDimensional
      (boostTupleLinear (F.boost_linear t) (q + 1))).comp (continuous_embedPlaneTuple _)
  have hRy : R y ∈ orderedTubeUnion q := by
    show complexBoostTuple (t : ℂ) (embedPlaneTuple y) ∈ _
    rw [← F.embedPlaneTuple_mapPoints]
    exact ht
  have hnh : R ⁻¹' orderedTubeUnion q ∈ 𝓝 y :=
    (F.union_isOpen.preimage hRc).mem_nhds hRy
  have hcont : ContinuousAt
      (fun y' => Complex.exp (-(4 * I * (h : ℂ) * (t : ℂ))) * indexHarmonic S φ₀ φ h (R y')) y :=
    continuousAt_const.mul (ContinuousAt.comp (g := indexHarmonic S φ₀ φ h) (f := R)
      ((continuousOn_of_holomorphicOnTuples (F.holomorphic φ h)).continuousAt
        (F.union_isOpen.mem_nhds hRy)) hRc.continuousAt)
  have heq : f =ᶠ[𝓝 y] fun y' =>
      Complex.exp (-(4 * I * (h : ℂ) * (t : ℂ))) * indexHarmonic S φ₀ φ h (R y') := by
    filter_upwards [hnh] with y' hy'
    have hord : mapPoints (rotate t) y' ∈ orderedRealTuples q := by
      show embedPlaneTuple (mapPoints (rotate t) y') ∈ orderedTubeUnion q
      rw [F.embedPlaneTuple_mapPoints]
      exact hy'
    rw [hf y' t hord]
    simp only [rotatedHarmonic]
    rw [F.embedPlaneTuple_mapPoints]
  exact (hcont.congr heq.symm).continuousWithinAt
def rotatedFunction (S : ConnFamily) (φ₀ : openingAngles) (φ : Fin (q + 1) → realLabels) (h : ℤ)
    (y : Fin (q + 1) → RealPlane) : ℂ :=
  rotatedHarmonic S φ₀ φ h
    (Classical.epsilon fun t : ℝ => mapPoints (rotate t) y ∈ orderedRealTuples q) y
theorem rotatedFunction_eq (F : Inputs S φ₀ q) (φ : Fin (q + 1) → realLabels) (h : ℤ)
    (y : Fin (q + 1) → RealPlane) (t : ℝ)
    (ht : mapPoints (rotate t) y ∈ orderedRealTuples q) :
    rotatedFunction S φ₀ φ h y = rotatedHarmonic S φ₀ φ h t y :=
  F.rotatedHarmonic_indep φ h (Classical.epsilon_spec (p := fun t : ℝ =>
    mapPoints (rotate t) y ∈ orderedRealTuples q) ⟨t, ht⟩) ht
theorem rotatedHarmonic_zero (F : Inputs S φ₀ q) (φ : Fin (q + 1) → realLabels) (h : ℤ)
    (y : Fin (q + 1) → RealPlane) :
    mapPoints (rotate 0) y = y ∧
      rotatedHarmonic S φ₀ φ h 0 y = indexHarmonic S φ₀ φ h (embedPlaneTuple y) := by
  have h0 : mapPoints (rotate 0) y = y := by
    funext i
    exact rotate_zero (y i)
  refine ⟨h0, ?_⟩
  simp only [rotatedHarmonic]
  rw [h0]
  simp
theorem rotatedFunction_extends (F : Inputs S φ₀ q) (φ : Fin (q + 1) → realLabels) (h : ℤ) :
    IsContinuousHarmonicExtension S φ₀ φ h (rotatedFunction S φ₀ φ h) := by
  refine ⟨F.continuousOn_of_rotated (F.rotatedFunction_eq φ h), fun y hy => ?_⟩
  obtain ⟨h0, h1⟩ := F.rotatedHarmonic_zero φ h y
  rw [F.rotatedFunction_eq φ h y 0 (by rw [h0]; exact hy), h1]
theorem extension_unique (F : Inputs S φ₀ q) {φ : Fin (q + 1) → realLabels}
    {h : ℤ} {f g : (Fin (q + 1) → RealPlane) → ℂ}
    (hf : IsContinuousHarmonicExtension S φ₀ φ h f)
    (hg : IsContinuousHarmonicExtension S φ₀ φ h g) :
    ∀ y ∈ injectivePointTuples (q + 1), f y = g y :=
  Set.EqOn.of_subset_closure (fun y hy => (hf.2 y hy).trans (hg.2 y hy).symm) hf.1 hg.1
    F.ordered_subset fun y _ => F.ordered_dense y
theorem distinctHarmonic_extends (F : Inputs S φ₀ q) (φ : Fin (q + 1) → realLabels) (h : ℤ) :
    IsContinuousHarmonicExtension S φ₀ φ h (distinctHarmonic S φ₀ φ h) :=
  Classical.epsilon_spec ⟨_, F.rotatedFunction_extends φ h⟩
theorem distinctHarmonic_eq_rotated (F : Inputs S φ₀ q) (φ : Fin (q + 1) → realLabels) (h : ℤ)
    (y : Fin (q + 1) → RealPlane) (t : ℝ)
    (ht : mapPoints (rotate t) y ∈ orderedRealTuples q) :
    distinctHarmonic S φ₀ φ h y = rotatedHarmonic S φ₀ φ h t y :=
  (F.extension_unique (F.distinctHarmonic_extends φ h) (F.rotatedFunction_extends φ h) y
    (F.injective_of_rotate_ordered ht)).trans (F.rotatedFunction_eq φ h y t ht)
theorem isLabelInvariant_distinct (F : Inputs S φ₀ q) (φ : Fin (q + 1) → realLabels)
    (h : ℤ) : IsLabelInvariant S φ₀ φ h := by
  intro ς y hy
  obtain ⟨t, ht⟩ := F.exists_rotate_ordered hy
  have hcomm : mapPoints (rotate t) (permuteTuple ς y) =
      permuteTuple ς (mapPoints (rotate t) y) := rfl
  have ht' : mapPoints (rotate t) (permuteTuple ς y) ∈ orderedRealTuples q := by
    rw [hcomm]
    exact (F.ordered_perm ς _).1 ht
  rw [F.distinctHarmonic_eq_rotated _ h _ t ht', F.distinctHarmonic_eq_rotated φ h _ t ht]
  simp only [rotatedHarmonic]
  have hinv := ((F.symmetry φ) h _ ht).1 ς
  have he : embedPlaneTuple (mapPoints (rotate t) (permuteTuple ς y)) =
      permuteTuple ς (embedPlaneTuple (mapPoints (rotate t) y)) := rfl
  rw [he]
  exact congrArg _ hinv
theorem isTranslationInvariant_distinct (F : Inputs S φ₀ q) (φ : Fin (q + 1) → realLabels)
    (h : ℤ) : IsTranslationInvariant S φ₀ φ h := by
  intro u y hy
  obtain ⟨t, ht⟩ := F.exists_rotate_ordered hy
  have hcomm : mapPoints (rotate t) (translateTuple y u) =
      translateTuple (mapPoints (rotate t) y) (rotate t u) :=
    funext fun i => rotate_add t (y i) u
  have ht' : mapPoints (rotate t) (translateTuple y u) ∈ orderedRealTuples q := by
    rw [hcomm]
    exact (F.ordered_translate _ _).1 ht
  rw [F.distinctHarmonic_eq_rotated φ h _ t ht', F.distinctHarmonic_eq_rotated φ h _ t ht]
  simp only [rotatedHarmonic]
  have hinv := (((F.symmetry φ) h _ ht).2.1) (embedPlane (rotate t u))
  have he : embedPlaneTuple (mapPoints (rotate t) (translateTuple y u)) =
      addConstTuple (embedPlaneTuple (mapPoints (rotate t) y))
        (embedPlane (rotate t u)) := by
    rw [hcomm]
    funext i
    simp [embedPlaneTuple, translateTuple, addConstTuple, embedPlane]
  rw [he]
  exact congrArg _ hinv
theorem isRotationCovariant_distinct (F : Inputs S φ₀ q) (φ : Fin (q + 1) → realLabels)
    (h : ℤ) : IsRotationCovariant S φ₀ φ h := by
  intro y hy t
  have hy' : mapPoints (rotate t) y ∈ injectivePointTuples (q + 1) :=
    fun i j e => hy (rotate_injective t e)
  obtain ⟨t', ht'⟩ := F.exists_rotate_ordered hy'
  have hrot : mapPoints (rotate t') (mapPoints (rotate t) y) =
      mapPoints (rotate (t' + t)) y :=
    funext fun i => rotate_rotate t' t (y i)
  have ht'' : mapPoints (rotate (t' + t)) y ∈ orderedRealTuples q := by
    rw [← hrot]
    exact ht'
  rw [F.distinctHarmonic_eq_rotated φ h _ t' ht', F.distinctHarmonic_eq_rotated φ h _ (t' + t) ht'']
  simp only [rotatedHarmonic]
  rw [hrot, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring
theorem vanishesAboveMaxFrequency_distinct (F : Inputs S φ₀ q) (φ : Fin (q + 1) → realLabels)
    (h : ℤ) : VanishesAboveMaxFrequency S φ₀ φ h := by
  intro hh y hy
  obtain ⟨t, ht⟩ := F.exists_rotate_ordered hy
  rw [F.distinctHarmonic_eq_rotated φ h _ t ht]
  simp [rotatedHarmonic, indexHarmonic, tubeUnionHarmonic, not_le.mpr hh]
end Inputs
theorem eqOn_of_isRealAnalyticTupleFun
    (hz : Analysis.VanishingOfRealAnalytic ((q + 1) * 2))
    {G W : Set (Fin (q + 1) → RealPlane)} (hGc : IsConnected G)
    (hW : IsOpen W) (hWne : W.Nonempty) (hWG : W ⊆ G)
    {f g : (Fin (q + 1) → RealPlane) → ℂ}
    (hf : IsRealAnalyticTupleFun G f) (hg : IsRealAnalyticTupleFun G g)
    (hfg : ∀ y ∈ W, f y = g y) : ∀ y ∈ G, f y = g y := by
  intro y hy
  let D : Set (ComplexCoordinates ((q + 1) * 2)) := pairTupleEquiv (q + 1) '' (embedPlaneTuple '' G)
  have hcont : Continuous fun y : Fin (q + 1) → RealPlane =>
      pairTupleEquiv (q + 1) (embedPlaneTuple y) :=
    (continuous_pairTupleEquiv _).comp (continuous_embedPlaneTuple _)
  have hDc : IsConnected D := by
    have himg := hGc.image _ hcont.continuousOn
    rwa [show (fun y : Fin (q + 1) → RealPlane =>
      pairTupleEquiv (q + 1) (embedPlaneTuple y)) '' G = D from (Set.image_image _ _ _).symm] at himg
  let d : ComplexCoordinates ((q + 1) * 2) → ℂ :=
    fun z => f (realTupleOf (q + 1) z) - g (realTupleOf (q + 1) z)
  have hana : ComplexCoordinates.IsRealAnalyticIn (N' := 1) D (fun z _ => d z) := by
    refine ⟨hf.1, ?_⟩
    intro a ha
    obtain ⟨c₁, h₁⟩ := hf.2 a ha
    obtain ⟨c₂, h₂⟩ := hg.2 a ha
    refine ⟨fun m => c₁ m - c₂ m, ?_⟩
    filter_upwards [h₁, h₂] with z hz₁ hz₂
    have hs := hz₁.sub hz₂
    simp only [← smul_sub] at hs
    have hd : (fun _ : Fin 1 => d z) = scalarEquiv (f (realTupleOf (q + 1) z)) -
        scalarEquiv (g (realTupleOf (q + 1) z)) := by
      funext j
      simp only [Pi.sub_apply, scalarEquiv_apply]
      rfl
    show HasSum _ (fun _ : Fin 1 => d z)
    rw [hd]
    exact hs
  have hW' : Matrices.ComplexMatrix2.IsRelativelyOpen D
      (pairTupleEquiv (q + 1) '' (embedPlaneTuple '' W)) := by
    refine ⟨realTupleOf (q + 1) ⁻¹' W, hW.preimage (continuous_realTupleOf _), ?_⟩
    ext z
    rw [mem_image_embed_iff, Set.mem_inter_iff, mem_image_embed_iff]
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₂, h₁, hWG h₂⟩, fun ⟨h₁, h₂, _⟩ => ⟨h₂, h₁⟩⟩
  have hzero := hz D hf.1 hDc d hana _ (hWne.image _ |>.image _) hW' (by
    intro x hx
    obtain ⟨_, hxW⟩ := (mem_image_embed_iff _ _).1 hx
    exact sub_eq_zero.mpr (hfg _ hxW)) (pairTupleEquiv (q + 1) (embedPlaneTuple y))
    ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  have hback : realTupleOf (q + 1) (pairTupleEquiv (q + 1) (embedPlaneTuple y)) = y := by
    simp [realTupleOf, tupleRe_embedPlaneTuple]
  simp only [d, hback] at hzero
  exact sub_eq_zero.mp hzero
theorem indexHarmonic_holomorphic {S : ConnFamily} {φ₀ : openingAngles}
    {φ : Fin (q + 1) → realLabels}
    (hD : IsOpen (orderedTubeUnion q))
    (hfam : ∀ h : ℤ, |h| ≤ (maxFrequency S φ₀ (q + 1) : ℤ) →
      HolomorphicOnTuples (orderedTubeUnion q) (harmonicFamily S φ₀ φ h))
    (h : ℤ) :
    HolomorphicOnTuples (orderedTubeUnion q) (indexHarmonic S φ₀ φ h) := by
  by_cases hh : |h| ≤ (maxFrequency S φ₀ (q + 1) : ℤ)
  · have he : indexHarmonic S φ₀ φ h = harmonicFamily S φ₀ φ h := by
      funext z
      simp [indexHarmonic, tubeUnionHarmonic, hh]
    rw [he]
    exact hfam h hh
  · have he : indexHarmonic S φ₀ φ h = fun _ => 0 := by
      funext z
      simp [indexHarmonic, tubeUnionHarmonic, hh]
    rw [he]
    have hopen : IsOpen (pairTupleEquiv (q + 1) '' orderedTubeUnion q) := by
      have hs : pairTupleEquiv (q + 1) '' orderedTubeUnion q =
          (pairTupleEquiv (q + 1)).symm ⁻¹' orderedTubeUnion q := by
        ext z
        exact mem_image_pairTupleEquiv_iff _ z
      rw [hs]
      exact hD.preimage (continuous_pairTupleEquiv_symm _)
    exact ⟨hopen, (continuousOn_const :
        ContinuousOn (fun _ : ComplexCoordinates ((q + 1) * 2) => scalarEquiv (0 : ℂ)) _),
      fun a _ j =>
      Eventually.of_forall fun ζ =>
        (differentiableAt_const (scalarEquiv (0 : ℂ)) :
          DifferentiableAt ℂ (fun _ : ℂ => scalarEquiv (0 : ℂ)) ζ)⟩
theorem holds
    (hrules : ForwardTube.RotationRules.Holds)
    (hone : UnionKernel.Holds)
    (hharm : TubeUnionHarmonics.Holds)
    (hcov : HarmonicRotationCovariance.Holds)
    (htools : Analysis.ZerosOfAnalyticMapsAndThinSets)
    (htop : MaxFrequencyFacts.Holds)
    (hseries : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    Holds := by
  intro m S d q hq h φ
  obtain ⟨-, -, -, -, -, hunion, -, hord⟩ := hone m S d q hq φ rightAngleZero rightAngleZero 1 1
  obtain ⟨ord_eq, -, -, -, ord_sub, -, -, -, ord_dense, ord_conn, ord_perm, ord_shift, -, pen_sub⟩ :=
    hord
  have hDopen : IsOpen (orderedTubeUnion q) := hunion.2.2.1
  obtain ⟨-, -, -, -, rot_lin, -, -, rot_formula, -, -, -⟩ := hrules.1
  have F : Inputs S d.angle q :=
    { ordered_eq := ord_eq
      ordered_subset := ord_sub
      ordered_dense := ord_dense
      ordered_isConnected := ord_conn
      ordered_perm := ord_perm
      ordered_translate := ord_shift
      pencil_subset := pen_sub
      union_isOpen := hDopen
      boost_formula := rot_formula
      boost_linear := fun ζ => (rot_lin ζ).1
      linear_holomorphic := fun N N' hN hN' f => (hrules.2.2.2.1.1 N N' hN hN').2 f
      series := hseries
      covariant := fun ψ => (hcov m S d q hq ψ).2.2
      holomorphic := fun ψ k =>
        indexHarmonic_holomorphic hDopen (hharm m S d q hq ψ).1.2.2 k
      symmetry := fun ψ => (hharm m S d q hq ψ).2.2.1 }
  have hG : IsOpen (injectivePointTuples (q + 1)) := isOpen_injectivePointTuples _
  have hGc : IsConnected (injectivePointTuples (q + 1)) :=
    F.ordered_isConnected.subset_closure F.ordered_subset fun y _ => F.ordered_dense y
  have hanalytic : ∀ (ψ : Fin (q + 1) → realLabels) (k : ℤ),
      IsRealAnalyticTupleFun (injectivePointTuples (q + 1))
        (distinctHarmonic S d.angle ψ k) :=
    fun ψ k => F.isRealAnalytic_of_rotated (F.distinctHarmonic_eq_rotated ψ k)
  have hpen : ∀ (ψ : Fin (q + 1) → realLabels) (k : ℤ), ∀ y ∈ pencilSet d.angle (q + 1),
      distinctHarmonic S d.angle ψ k y = angleHarmonic S d.angle y ψ k :=
    fun ψ k y hy => ((F.distinctHarmonic_extends ψ k).2 y (F.pencil_subset hy)).trans
      ((hharm m S d q hq ψ).2.1 y hy k)
  obtain ⟨hPenOpen, hPenMem⟩ := hrules.2.2.2.2.2 d.angle |>.2.2.2.2 q hq
  refine ⟨⟨F.distinctHarmonic_extends φ h, fun f hf y hy =>
      F.extension_unique hf (F.distinctHarmonic_extends φ h) y hy⟩,
    ⟨hanalytic φ h, hGc, hG⟩, F.isLabelInvariant_distinct φ h, F.isTranslationInvariant_distinct φ h,
    F.isRotationCovariant_distinct φ h, ?_, F.vanishesAboveMaxFrequency_distinct φ h, ?_, hPenOpen,
    hpen φ h, ?_⟩
  · intro y hy
    exact (Finset.sum_congr rfl fun k _ => (F.distinctHarmonic_extends φ k).2 y hy).trans
      ((hharm m S d q hq φ).2.2.2 _ hy)
  · intro h1
    obtain ⟨-, hx⟩ := (htop m S d).2.2 (q + 1) h1
    obtain ⟨y, hy, ψ, hne⟩ := hx q rfl
    refine ⟨ψ, y, F.ordered_subset (F.pencil_subset hy), ?_⟩
    rw [hpen ψ _ y hy]
    exact hne
  · intro f hf hfp y hy
    exact eqOn_of_isRealAnalyticTupleFun ((htools ((q + 1) * 2) (by omega)).2.1) hGc hPenOpen
      ⟨_, hPenMem⟩ (fun y hy => F.ordered_subset (F.pencil_subset hy)) hf (hanalytic φ h)
      (fun y hy => (hfp y hy).trans (hpen φ h y hy).symm) y hy
end YangMills.Construction.EuclideanFunctionals.DistinctHarmonics
end
