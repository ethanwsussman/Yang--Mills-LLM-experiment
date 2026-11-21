import YangMills.Construction.Matrices.CalculusOfHolomorphicMapsProof
import YangMills.Construction.RotationInvariance.EntireFunctionOfTheAngleOnAPencilProof
import YangMills.Construction.RotationInvariance.FunctionalAndPlaneKernelsAreLinearInEachLabel
import YangMills.Construction.RotationInvariance.HarmonicsOnTheUnionOfTheTubesProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Complex (I)
open RealPlane ForwardTube MeasureTheory Filter
open Matrices.GroupLieProduct.Subspaces.AnalyticCalculus (scalarEquiv)
open scoped Topology
namespace EuclideanFunctionals.UnionKernel
open ForwardTube.RotationRules
variable {q : ℕ}
theorem pairTupleEquiv_add (p : ℕ) (a b : Fin p → ℂ × ℂ) :
    pairTupleEquiv p (a + b) = pairTupleEquiv p a + pairTupleEquiv p b := by
  funext k
  obtain ⟨⟨i, c⟩, rfl⟩ := finProdFinEquiv.surjective k
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  · simp [pairTupleEquiv_apply_fst]
  · simp [pairTupleEquiv_apply_snd]
theorem pairTupleEquiv_smul (p : ℕ) (c : ℂ) (a : Fin p → ℂ × ℂ) :
    pairTupleEquiv p (c • a) = c • pairTupleEquiv p a := by
  funext k
  obtain ⟨⟨i, d⟩, rfl⟩ := finProdFinEquiv.surjective k
  rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
  · simp [pairTupleEquiv_apply_fst]
  · simp [pairTupleEquiv_apply_snd]
def pairTupleLinearEquiv (p : ℕ) : (Fin p → ℂ × ℂ) ≃ₗ[ℂ] Coordinates.ComplexCoordinates (p * 2) :=
  { pairTupleEquiv p with
    map_add' := pairTupleEquiv_add p
    map_smul' := pairTupleEquiv_smul p }
theorem continuous_pairTupleEquiv (p : ℕ) : Continuous (pairTupleEquiv p) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TwoPointTopFrequency.continuous_pairTupleEquiv <;> assumption
theorem isOpen_pairTupleEquiv_image {p : ℕ} {O : Set (Fin p → ℂ × ℂ)} (hO : IsOpen O) :
    IsOpen (pairTupleEquiv p '' O) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TubeUnionHarmonicsProof.isOpen_image_pairTupleEquiv <;> assumption
theorem holomorphicOnTuples_iff {p : ℕ} {O : Set (Fin p → ℂ × ℂ)} {f : (Fin p → ℂ × ℂ) → ℂ} :
    HolomorphicOnTuples O f ↔ Coordinates.ComplexCoordinates.IsHolomorphicIn
      (pairTupleEquiv p '' O) (scalarEquiv ∘ f ∘ (pairTupleEquiv p).symm) :=
  Iff.rfl
theorem scalarEquiv_apply (z : ℂ) (j : Fin 1) : scalarEquiv z j = z := by apply _root_.YangMills.DeltaSharedProofs.p23888 <;> assumption
theorem continuousOn_of_holomorphicOnTuples {p : ℕ} {O : Set (Fin p → ℂ × ℂ)}
    {f : (Fin p → ℂ × ℂ) → ℂ} (hf : HolomorphicOnTuples O f) : ContinuousOn f O := by apply _root_.YangMills.Construction.EuclideanFunctionals.HarmonicRotationCovariance.continuousOn_of_holomorphicOnTuples <;> assumption
theorem holomorphicOnTuples_of_locally {p : ℕ} {O : Set (Fin p → ℂ × ℂ)} (hO : IsOpen O)
    {f : (Fin p → ℂ × ℂ) → ℂ}
    (h : ∀ a ∈ O, ∃ (U : Set (Fin p → ℂ × ℂ)) (g : (Fin p → ℂ × ℂ) → ℂ), a ∈ U ∧
      HolomorphicOnTuples U g ∧ ∀ z ∈ U, f z = g z) :
    HolomorphicOnTuples O f := by
  refine ⟨isOpen_pairTupleEquiv_image hO, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨U, g, haU, hg, hfg⟩ := h a ha
    have hU := (holomorphicOnTuples_iff.1 hg).1
    have hn : pairTupleEquiv p '' U ∈ 𝓝 (pairTupleEquiv p a) :=
      hU.mem_nhds ⟨a, haU, rfl⟩
    have hc : ContinuousAt (scalarEquiv ∘ g ∘ (pairTupleEquiv p).symm)
        (pairTupleEquiv p a) :=
      (holomorphicOnTuples_iff.1 hg).2.1.continuousAt hn
    refine (hc.congr ?_).continuousWithinAt
    filter_upwards [hn] with w hw
    obtain ⟨z, hz, rfl⟩ := hw
    simp [hfg z hz]
  · rintro _ ⟨a, ha, rfl⟩ j
    obtain ⟨U, g, haU, hg, hfg⟩ := h a ha
    have hU := (holomorphicOnTuples_iff.1 hg).1
    have hd := (holomorphicOnTuples_iff.1 hg).2.2 _ ⟨a, haU, rfl⟩ j
    have hcont : Continuous fun ζ : ℂ =>
        pairTupleEquiv p a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j := by
      fun_prop
    have hW : ∀ᶠ ζ in 𝓝 (0 : ℂ),
        pairTupleEquiv p a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j ∈
        pairTupleEquiv p '' U := by
      apply hcont.continuousAt.eventually_mem
      simpa using hU.mem_nhds ⟨a, haU, rfl⟩
    filter_upwards [hd, hW.eventually_nhds] with ζ hζ hζ'
    refine hζ.congr_of_eventuallyEq ?_
    filter_upwards [hζ'] with ζ' hz
    obtain ⟨z, hz, hzz⟩ := hz
    simp [← hzz, hfg z hz]
theorem holomorphicOnTuples_sub {p : ℕ} {O : Set (Fin p → ℂ × ℂ)} {f g : (Fin p → ℂ × ℂ) → ℂ}
    (hf : HolomorphicOnTuples O f) (hg : HolomorphicOnTuples O g) :
    HolomorphicOnTuples O fun z => f z - g z := by
  have h1 := holomorphicOnTuples_iff.1 hf
  have h2 := holomorphicOnTuples_iff.1 hg
  have he : (scalarEquiv ∘ (fun z => f z - g z) ∘ (pairTupleEquiv p).symm) =
      (scalarEquiv ∘ f ∘ (pairTupleEquiv p).symm) -
        (scalarEquiv ∘ g ∘ (pairTupleEquiv p).symm) := by
    funext w j
    simp [scalarEquiv_apply]
  refine holomorphicOnTuples_iff.2 ?_
  rw [he]
  refine ⟨h1.1, h1.2.1.sub h2.2.1, fun a ha j => ?_⟩
  filter_upwards [h1.2.2 a ha j, h2.2.2 a ha j] with ζ h₁ h₂
  exact h₁.sub h₂
theorem holomorphicOnTuples_comp_linearMap
    (hr : AffineAndRotationHolomorphy)
    (hh : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) {p p' : ℕ}
    (hp : 1 ≤ p) (hp' : 1 ≤ p')
    (L : (Fin p → ℂ × ℂ) →ₗ[ℂ] (Fin p' → ℂ × ℂ)) {O : Set (Fin p' → ℂ × ℂ)}
    {f : (Fin p' → ℂ × ℂ) → ℂ} (hf : HolomorphicOnTuples O f) :
    HolomorphicOnTuples (L ⁻¹' O) (f ∘ L) := by
  have hf' := holomorphicOnTuples_iff.1 hf
  let L' : Coordinates.ComplexCoordinates (p * 2) →ₗ[ℂ] Coordinates.ComplexCoordinates (p' * 2) :=
    (pairTupleLinearEquiv p').toLinearMap ∘ₗ L ∘ₗ (pairTupleLinearEquiv p).symm.toLinearMap
  have hL := (hr.1 (p * 2) (p' * 2) (by omega) (by omega)).2 L'
  have hOp : IsOpen (L ⁻¹' O) := by
    have hc : Continuous L := L.continuous_of_finiteDimensional
    have hOo : IsOpen O := by
      have := hf'.1.preimage (continuous_pairTupleEquiv p')
      rwa [Set.preimage_image_eq _ (pairTupleEquiv p').injective] at this
    exact hOo.preimage hc
  have hL' : Coordinates.ComplexCoordinates.IsHolomorphicIn (pairTupleEquiv p '' (L ⁻¹' O)) L' :=
    ⟨isOpen_pairTupleEquiv_image hOp, hL.2.1.mono (Set.subset_univ _),
      fun a _ j => hL.2.2 a trivial j⟩
  have hmaps : Set.MapsTo L' (pairTupleEquiv p '' (L ⁻¹' O)) (pairTupleEquiv p' '' O) := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨L z, hz, ?_⟩
    show pairTupleEquiv p' (L z) =
      pairTupleEquiv p' (L ((pairTupleEquiv p).symm (pairTupleEquiv p z)))
    simp
  have hcomp := (((hh.1 (p' * 2) _ hf'.1).1 1 _ hf').2.2.2.1 (p * 2) _ L' hL' hmaps)
  refine holomorphicOnTuples_iff.2 ?_
  convert hcomp using 1
  funext w
  show scalarEquiv (f (L ((pairTupleEquiv p).symm w))) =
    scalarEquiv (f ((pairTupleEquiv p').symm (pairTupleEquiv p'
      (L ((pairTupleEquiv p).symm w)))))
  simp
def permutedDifferencesLinear (ς : Equiv.Perm (Fin (q + 1))) :
    (Fin (q + 1) → ℂ × ℂ) →ₗ[ℂ] (Fin q → ℂ × ℂ) where
  toFun z := complexDifferences (permuteTuple ς z)
  map_add' a b := by
    funext i
    simp only [complexDifferences, permuteTuple, Pi.add_apply]
    abel
  map_smul' c a := by
    funext i
    simp only [complexDifferences, permuteTuple, Pi.smul_apply, RingHom.id_apply, smul_sub]
theorem orderedTube_eq_preimage (υ : rightAngleMultiples) (ς : Equiv.Perm (Fin (q + 1))) :
    orderedTube υ ς = permutedDifferencesLinear ς ⁻¹' rotatedTubePow υ q := by
  ext z
  exact mem_orderedTube_iff υ ς z
theorem orderedFrameKernel_holomorphic (hr : AffineAndRotationHolomorphy)
    (hh : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) {S : ConnFamily}
    (hq : 1 ≤ q) {υ : rightAngleMultiples} {ς : Equiv.Perm (Fin (q + 1))}
    {φ : Fin (q + 1) → realLabels}
    (hframe : PlaneKernelProps.RotatedFrameRep S (permuteTuple ς φ) υ) :
    HolomorphicOnTuples (orderedTube υ ς)
      (fun z => orderedFrameKernel S υ ς z φ) := by
  rw [orderedTube_eq_preimage]
  exact holomorphicOnTuples_comp_linearMap hr hh (by omega) hq (permutedDifferencesLinear ς)
    hframe.2.1
theorem embedPlane_sub (a b : RealPlane) : embedPlane a - embedPlane b = embedPlane (a - b) := by
  simp [embedPlane]
theorem embedPlane_vecRe_sub (a b : ℂ × ℂ) :
    embedPlane (vecRe a) - embedPlane (vecRe b) = embedPlane (vecRe (a - b)) := by
  simp [embedPlane, vecRe]
theorem isOpen_orderedTube (hF : TubeAndRotatedTubeRules) (υ : rightAngleMultiples)
    (ς : Equiv.Perm (Fin (q + 1))) : IsOpen (orderedTube υ ς) := by
  have he : orderedTube υ ς =
      ⋂ i : Fin q, (fun z : Fin (q + 1) → ℂ × ℂ => z (ς i.succ) - z (ς i.castSucc)) ⁻¹'
        rotatedForwardTube υ := by
    ext z
    simp [orderedTube]
  rw [he]
  exact isOpen_iInter_of_finite fun i => ((hF.2.2.1 υ).1).preimage (by fun_prop)
theorem orderedTube_stableOpenCone (hL : LightConeAndComplexRotationRules)
    (hF : TubeAndRotatedTubeRules) (υ : rightAngleMultiples)
    (ς : Equiv.Perm (Fin (q + 1))) : StableOpenCone υ ς := by
  obtain ⟨-, hconv, hcone, hrot, hre, -⟩ := hF.2.2.1 υ
  refine ⟨isOpen_orderedTube hF υ ς, ?_, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab i
    have h := hconv (hx i) (hy i) ha hb hab
    have he : (a • x + b • y) (ς i.succ) - (a • x + b • y) (ς i.castSucc) =
        a • (x (ς i.succ) - x (ς i.castSucc)) + b • (y (ς i.succ) - y (ς i.castSucc)) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_sub]
      abel
    rw [he]
    exact h
  · intro z hz l hl i
    have he : (l • z) (ς i.succ) - (l • z) (ς i.castSucc) =
        l • (z (ς i.succ) - z (ς i.castSucc)) := by
      simp only [Pi.smul_apply, smul_sub]
    rw [he]
    exact hcone _ (hz i) l hl
  · intro z hz
    refine ⟨fun u i => ?_, fun s i => ?_, fun i => ?_⟩
    · have he : addConstTuple z u (ς i.succ) - addConstTuple z u (ς i.castSucc) =
          z (ς i.succ) - z (ς i.castSucc) := by
        simp [addConstTuple]
      rw [he]
      exact hz i
    · have he : imagBoostTuple s z (ς i.succ) -
          imagBoostTuple s z (ς i.castSucc) =
          complexBoost (I * (s : ℂ)) (z (ς i.succ) - z (ς i.castSucc)) :=
        (((hL.2.2.2.2.1 (I * (s : ℂ))).1).mk' _).map_sub _ _ |>.symm
      rw [he, ← hrot s]
      exact ⟨_, hz i, rfl⟩
    · have he : embedPlaneTuple (tupleRe z) (ς i.succ) -
          embedPlaneTuple (tupleRe z) (ς i.castSucc) =
          embedPlane (vecRe (z (ς i.succ) - z (ς i.castSucc))) :=
        embedPlane_vecRe_sub _ _
      rw [he]
      exact hre _ (hz i)
theorem embedPlaneTuple_mem_orderedTube_iff (hF : TubeAndRotatedTubeRules)
    (υ : rightAngleMultiples) (ς : Equiv.Perm (Fin (q + 1))) (y : Fin (q + 1) → RealPlane) :
    embedPlaneTuple y ∈ orderedTube υ ς ↔
      ∀ i : Fin q, inner ℝ (rotatedDirection υ) (y (ς i.castSucc)) <
        inner ℝ (rotatedDirection υ) (y (ς i.succ)) := by
  have hdir := (hF.2.2.1 υ).2.2.2.2.2
  refine forall_congr' fun i => ?_
  have he : embedPlaneTuple y (ς i.succ) - embedPlaneTuple y (ς i.castSucc) =
      embedPlane (y (ς i.succ) - y (ς i.castSucc)) := embedPlane_sub _ _
  rw [he, hdir, inner_sub_right]
  constructor <;> intro h <;> linarith
theorem strictMono_of_embedPlaneTuple_mem (hF : TubeAndRotatedTubeRules)
    {υ : rightAngleMultiples} {ς : Equiv.Perm (Fin (q + 1))} {y : Fin (q + 1) → RealPlane}
    (h : embedPlaneTuple y ∈ orderedTube υ ς) :
    StrictMono fun i => inner ℝ (rotatedDirection υ) (y (ς i)) :=
  Fin.strictMono_iff_lt_succ.2 ((embedPlaneTuple_mem_orderedTube_iff hF υ ς y).1 h)
theorem realLocusOrdered_holds (hF : TubeAndRotatedTubeRules) (υ : rightAngleMultiples)
    (ς : Equiv.Perm (Fin (q + 1))) : RealLocusOrdered υ ς := by
  ext v
  constructor
  · rintro ⟨hv, y, hy⟩
    have hvy : v = embedPlaneTuple y := funext hy
    subst hvy
    exact ⟨y, (embedPlaneTuple_mem_orderedTube_iff hF υ ς y).1 hv, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(embedPlaneTuple_mem_orderedTube_iff hF υ ς y).2 hy, y, fun _ => rfl⟩
theorem exists_tuple_in_supports {α : Fin (q + 1) → RealPlane → ℂ}
    (hnon : ∀ i, (tsupport (α i)).Nonempty) {a b : Fin (q + 1)} (hab : a ≠ b)
    {x x' : RealPlane} (hx : x ∈ tsupport (α a)) (hx' : x' ∈ tsupport (α b)) :
    ∃ y : Fin (q + 1) → RealPlane, (∀ i, y i ∈ tsupport (α i)) ∧ y a = x ∧ y b = x' := by
  choose c hc using hnon
  refine ⟨Function.update (Function.update c a x) b x', fun i => ?_, ?_, ?_⟩
  · by_cases h1 : i = b
    · subst h1
      simpa using hx'
    · by_cases h2 : i = a
      · subst h2
        simpa [Function.update_of_ne h1] using hx
      · simpa [Function.update_of_ne h1, Function.update_of_ne h2] using hc i
  · simp [Function.update_of_ne hab]
  · simp
theorem tsupport_nonempty_of_ne_zero {α : RealPlane → ℂ} (h : α ≠ 0) : (tsupport α).Nonempty := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h
  exact ⟨x, subset_tsupport _ hx⟩
theorem pairwise_disjoint_tsupport (hF : TubeAndRotatedTubeRules) {υ : rightAngleMultiples}
    {ς : Equiv.Perm (Fin (q + 1))} {α : Fin (q + 1) → RealPlane → ℂ} (hne : ∀ i, α i ≠ 0)
    (hsub : ∀ y : Fin (q + 1) → RealPlane, (∀ i, y i ∈ tsupport (α i)) →
      embedPlaneTuple y ∈ orderedTube υ ς) :
    Pairwise fun i j => Disjoint (tsupport (α i)) (tsupport (α j)) := by
  intro a b hab
  rw [Set.disjoint_left]
  intro x ha hb
  obtain ⟨y, hy, h1, h2⟩ :=
    exists_tuple_in_supports (fun i => tsupport_nonempty_of_ne_zero (hne i)) hab ha hb
  have hs := strictMono_of_embedPlaneTuple_mem hF (hsub y hy)
  have hi : ς.symm a ≠ ς.symm b := fun h => hab (ς.symm.injective h)
  have hn := hs.injective.ne hi
  simp [h1, h2] at hn
theorem funsDirectionSeparated_of_subset (hF : TubeAndRotatedTubeRules)
    {υ : rightAngleMultiples} {ς : Equiv.Perm (Fin (q + 1))}
    {α : Fin (q + 1) → RealPlane → ℂ} (hc : ∀ i, HasCompactSupport (α i))
    (hne : ∀ i, α i ≠ 0)
    (hsub : ∀ y : Fin (q + 1) → RealPlane, (∀ i, y i ∈ tsupport (α i)) →
      embedPlaneTuple y ∈ orderedTube υ ς) :
    FunsDirectionSeparated υ fun i => α (ς i) := by
  have hnon : ∀ i, (tsupport (α i)).Nonempty := fun i => tsupport_nonempty_of_ne_zero (hne i)
  refine ⟨fun i => hc _, fun i => hne _, fun i => hc _, fun i => hnon _, fun i hi => ?_⟩
  let i' : Fin q := ⟨i, by omega⟩
  have e1 : (⟨i, Nat.lt_of_succ_lt hi⟩ : Fin (q + 1)) = i'.castSucc := rfl
  have e2 : (⟨i + 1, hi⟩ : Fin (q + 1)) = i'.succ := rfl
  show supInner _ (tsupport (α (ς ⟨i, Nat.lt_of_succ_lt hi⟩))) <
    infInner _ (tsupport (α (ς ⟨i + 1, hi⟩)))
  rw [e1, e2]
  obtain ⟨⟨a, ha, hae⟩, -⟩ :=
    isGreatest_supInner (rotatedDirection υ) (hc (ς i'.castSucc)) (hnon _)
  obtain ⟨⟨b, hb, hbe⟩, -⟩ := isLeast_infInner (rotatedDirection υ) (hc (ς i'.succ)) (hnon _)
  rw [← hae, ← hbe]
  have hab : ς i'.castSucc ≠ ς i'.succ :=
    fun h => (Fin.castSucc_lt_succ (i := i')).ne (ς.injective h)
  obtain ⟨y, hy, h1, h2⟩ := exists_tuple_in_supports hnon hab ha hb
  have h := (embedPlaneTuple_mem_orderedTube_iff hF υ ς y).1 (hsub y hy) i'
  rw [h1, h2] at h
  exact h
theorem profileIntegrand_permute (ς : Equiv.Perm (Fin (q + 1)))
    (α : Fin (q + 1) → RealPlane → ℂ) (F : (Fin (q + 1) → RealPlane) → ℂ)
    (y : Fin (q + 1) → RealPlane) :
    profileIntegrand (fun i => α (ς i)) F (permuteTuple ς y) =
      profileIntegrand α (fun y => F (permuteTuple ς y)) y := by
  unfold profileIntegrand
  have hm : permuteTuple ς y ∈ Set.univ.pi (fun i => tsupport (α (ς i))) ↔
      y ∈ Set.univ.pi fun i => tsupport (α i) := by
    simp only [Set.mem_univ_pi, permuteTuple]
    exact ⟨fun h j => by simpa using h (ς.symm j), fun h i => h (ς i)⟩
  by_cases hy : y ∈ Set.univ.pi fun i => tsupport (α i)
  · rw [Set.indicator_of_mem (hm.2 hy), Set.indicator_of_mem hy]
    congr 1
    exact Equiv.prod_comp ς fun j => α j (y j)
  · rw [Set.indicator_of_notMem (fun h => hy (hm.1 h)), Set.indicator_of_notMem hy]
theorem integral_permuteTuple (ς : Equiv.Perm (Fin (q + 1)))
    (G : (Fin (q + 1) → RealPlane) → ℂ) :
    ∫ y, G (permuteTuple ς y) = ∫ y, G y := by
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin (q + 1) => RealPlane) ς.symm
  have hT : ∀ y : Fin (q + 1) → RealPlane,
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (q + 1) => RealPlane) ς.symm) y =
        permuteTuple ς y := by
    intro y
    funext a
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, permuteTuple]
  rw [← hmp.integral_comp' G]
  simp only [hT]
theorem integralRepresentation_holds {m : SharpScale} {S : ConnFamily}
    (d : PlaneDataWithAperture m S)
    (hF : TubeAndRotatedTubeRules)
    (hmul : LabelLinearity.Holds)
    (hkern : PlaneKernelProps.Holds)
    (hinv : MomentSymmetry.ReductionHolds) (hq : 1 ≤ q)
    (υ : rightAngleMultiples) (ς : Equiv.Perm (Fin (q + 1))) (φ : Fin (q + 1) → realLabels) :
    IntegralRepresentation S υ ς φ := by
  intro α hα hsub
  have hc : ∀ i, HasCompactSupport (α i) := fun i => (hα i).2
  refine ⟨fun hne => pairwise_disjoint_tsupport hF hne hsub, fun hdis => ?_⟩
  obtain ⟨hent, -, hzero⟩ := (hmul m S d q hq φ 0 (φ 0) 0 0).1 α hα hdis
  refine ⟨hent, ?_⟩
  by_cases h0 : ∃ l, α l = 0
  · rw [hzero h0]
    obtain ⟨l, hl⟩ := h0
    have hp : ∀ y : Fin (q + 1) → RealPlane, (∏ i, α i (y i)) = 0 :=
      fun y => Finset.prod_eq_zero (Finset.mem_univ l) (by simp [hl])
    simp [profileIntegral, profileIntegrand, hp]
  · push Not at h0
    have hord := funsDirectionSeparated_of_subset hF hc h0 hsub
    have hsym := (hinv m S d.base.sigma).1 (q + 1) (by omega) ς
      (fun i => productFunction (α i) (φ i)) hent
    have hfr := (hkern m S d q hq (permuteTuple ς φ)).2.2.2.2.2 υ
    have hint := hfr.2.2 (fun i => α (ς i)) (fun i => hα _) hord
    have e1 : centeredFnAtProducts S α φ =
        centeredFnAtProducts S (fun i => α (ς i)) (permuteTuple ς φ) := hsym.symm
    rw [e1, hint]
    unfold differenceIntegral profileIntegral
    rw [← integral_permuteTuple ς]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only []
    rw [profileIntegrand_permute]
    congr 1
    funext y'
    show _ = planeKernel S (permuteTuple ς φ) (unrotate υ
      (complexDifferences (embedPlaneTuple (permuteTuple ς y'))))
    rw [complexDifferences_embedPlaneTuple]
theorem continuous_embedPlane : Continuous embedPlane := by apply _root_.YangMills.Construction.ForwardTube.ProductIntegralDetermination.continuous_embedPlane <;> assumption
theorem continuous_embedPlaneTuple : Continuous (embedPlaneTuple (q := q + 1)) :=
  continuous_pi fun i => continuous_embedPlane.comp (continuous_apply i)
theorem integrable_profileIntegrand {n : ℕ} {α : Fin n → RealPlane → ℂ}
    (hα : ∀ i, Continuous (α i)) (hc : ∀ i, HasCompactSupport (α i))
    {f : (Fin n → RealPlane) → ℂ}
    (hf : ContinuousOn f (Set.univ.pi fun i => tsupport (α i))) :
    Integrable (profileIntegrand α f) := by apply _root_.YangMills.Construction.EuclideanFunctionals.AngleFunctionOnPencil.integrable_profileIntegrand <;> assumption
theorem weightedIntegral_sub_eq_zero {S : ConnFamily} {O : Set (Fin (q + 1) → RealPlane)}
    {φ : Fin (q + 1) → realLabels} {F₁ F₂ : (Fin (q + 1) → RealPlane) → ℂ}
    (hO₁ : ContinuousOn F₁ O) (hO₂ : ContinuousOn F₂ O)
    (hI₁ : ∀ α : Fin (q + 1) → RealPlane → ℂ, (∀ i, α i ∈ complexProfiles) →
      (∀ y : Fin (q + 1) → RealPlane, (∀ i, y i ∈ tsupport (α i)) → y ∈ O) →
      (∀ i, α i ≠ 0) → centeredFnAtProducts S α φ = profileIntegral α F₁)
    (hI₂ : ∀ α : Fin (q + 1) → RealPlane → ℂ, (∀ i, α i ∈ complexProfiles) →
      (∀ y : Fin (q + 1) → RealPlane, (∀ i, y i ∈ tsupport (α i)) → y ∈ O) →
      (∀ i, α i ≠ 0) → centeredFnAtProducts S α φ = profileIntegral α F₂)
    (α : Fin (q + 1) → RealPlane → ℝ) (hα : IsSmoothTestFamilyIn O α) :
    productWeightedIntegral O α (fun y => F₁ y - F₂ y) = 0 := by
  obtain ⟨hsm, hcs, hsub⟩ := hα
  by_cases h0 : ∃ i, α i = 0
  · obtain ⟨i, hi⟩ := h0
    have hz : ∀ y : Fin (q + 1) → RealPlane, (∏ a, ((α a (y a) : ℝ) : ℂ)) = 0 :=
      fun y => Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    simp [productWeightedIntegral, Set.indicator, hz]
  · push Not at h0
    let β : Fin (q + 1) → RealPlane → ℂ := fun i y => (α i y : ℂ)
    have hts : ∀ i, tsupport (β i) = tsupport (α i) := by
      intro i
      unfold tsupport
      congr 1
      ext y
      simp [β, Function.mem_support]
    have hβp : ∀ i, β i ∈ complexProfiles := fun i =>
      ⟨Complex.ofRealCLM.contDiff.comp ((hsm i).of_le (by simp)),
        (hcs i).comp_left Complex.ofReal_zero⟩
    have hβc : ∀ i, HasCompactSupport (β i) := fun i => (hβp i).2
    have hβne : ∀ i, β i ≠ 0 := by
      intro i h
      apply h0 i
      funext y
      have h1 := congrFun h y
      simpa [β] using h1
    have hP : (Set.univ.pi fun i => tsupport (β i)) = Set.univ.pi fun i => tsupport (α i) := by
      simp only [hts]
    have hsub' : (Set.univ.pi fun i => tsupport (β i)) ⊆ O := hP ▸ hsub
    have hsub'' : ∀ y : Fin (q + 1) → RealPlane, (∀ i, y i ∈ tsupport (β i)) → y ∈ O :=
      fun y hy => hsub' fun i _ => hy i
    have eI : profileIntegral β F₁ = profileIntegral β F₂ :=
      (hI₁ β hβp hsub'' hβne).symm.trans (hI₂ β hβp hsub'' hβne)
    have i₁ : Integrable (profileIntegrand β F₁) :=
      integrable_profileIntegrand (fun i => (hβp i).1.continuous) hβc (hO₁.mono hsub')
    have i₂ : Integrable (profileIntegrand β F₂) :=
      integrable_profileIntegrand (fun i => (hβp i).1.continuous) hβc (hO₂.mono hsub')
    have hpt : (fun y => O.indicator
        (fun y => (∏ a, ((α a (y a) : ℝ) : ℂ)) * (F₁ y - F₂ y)) y) =
        fun y => profileIntegrand β F₁ y - profileIntegrand β F₂ y := by
      funext y
      unfold profileIntegrand
      by_cases hy : y ∈ Set.univ.pi fun i => tsupport (β i)
      · rw [Set.indicator_of_mem (hsub' hy), Set.indicator_of_mem hy, Set.indicator_of_mem hy]
        simp only [β]
        ring
      · obtain ⟨i, hi⟩ : ∃ i, y i ∉ tsupport (β i) := by
          simpa [Set.mem_pi] using hy
        rw [hts] at hi
        have hzi : α i (y i) = 0 := image_eq_zero_of_notMem_tsupport hi
        have hz : (∏ a, ((α a (y a) : ℝ) : ℂ)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hzi])
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
        simp [Set.indicator, hz]
    unfold productWeightedIntegral
    rw [hpt, integral_sub i₁ i₂]
    exact sub_eq_zero.2 eI
theorem pairTupleEquiv_embed_tupleRe {p : ℕ} (z : Fin p → ℂ × ℂ) :
    pairTupleEquiv p (embedPlaneTuple (tupleRe z)) =
      fun j => ((pairTupleEquiv p z j).re : ℂ) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TubeUnionHarmonicsProof.pairTupleEquiv_embed_tupleRe <;> assumption
theorem eq_embed_tupleRe_of_mem_realLocus {p : ℕ} {z : Fin p → ℂ × ℂ}
    (h : pairTupleEquiv p z ∈ Coordinates.ComplexCoordinates.realLocus (p * 2)) :
    z = embedPlaneTuple (tupleRe z) := by
  apply (pairTupleEquiv p).injective
  rw [pairTupleEquiv_embed_tupleRe]
  funext k
  apply Complex.ext
  · simp
  · simpa using h k
theorem eq_zero_of_eq_zero_on_real {p : ℕ} (hz : Analysis.VanishingFromRealPoints (p * 2))
    {D : Set (Fin p → ℂ × ℂ)} (hD : IsOpen D) (hc : Convex ℝ D)
    (hre : ∀ z ∈ D, embedPlaneTuple (tupleRe z) ∈ D) {g : (Fin p → ℂ × ℂ) → ℂ}
    (hg : HolomorphicOnTuples D g)
    (hreal : ∀ y, embedPlaneTuple y ∈ D → g (embedPlaneTuple y) = 0) :
    ∀ z ∈ D, g z = 0 := by
  intro z hzD
  have hconv : Convex ℝ (pairTupleEquiv p '' D) :=
    hc.linear_image ((pairTupleLinearEquiv p).toLinearMap.restrictScalars ℝ)
  have hre' : ∀ w ∈ pairTupleEquiv p '' D,
      (fun j => ((w j).re : ℂ) : Coordinates.ComplexCoordinates (p * 2)) ∈
        pairTupleEquiv p '' D := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨_, hre x hx, pairTupleEquiv_embed_tupleRe x⟩
  have hhol : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) (pairTupleEquiv p '' D)
      (fun w _ => g ((pairTupleEquiv p).symm w)) := by
    convert holomorphicOnTuples_iff.1 hg using 1
    funext w j
    simp [scalarEquiv_apply]
  have hw := hz (pairTupleEquiv p '' D) (isOpen_pairTupleEquiv_image hD) hconv hre'
    (fun w => g ((pairTupleEquiv p).symm w)) hhol
    (pairTupleEquiv p '' D ∩ Coordinates.ComplexCoordinates.realLocus (p * 2))
    ⟨pairTupleEquiv p (embedPlaneTuple (tupleRe z)),
      ⟨_, hre z hzD, rfl⟩, fun j => by rw [pairTupleEquiv_embed_tupleRe]; simp⟩
    (fun x hx => hx) ⟨_, isOpen_pairTupleEquiv_image hD, rfl⟩
    (by
      rintro _ ⟨⟨x, hx, rfl⟩, hxr⟩
      have hxe := eq_embed_tupleRe_of_mem_realLocus hxr
      simp only [Equiv.symm_apply_apply]
      rw [hxe]
      exact hreal _ (hxe ▸ hx))
    (pairTupleEquiv p z) ⟨z, hzD, rfl⟩
  simpa using hw
theorem agreeOnOverlaps_holds {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S)
    (hL : LightConeAndComplexRotationRules) (hF : TubeAndRotatedTubeRules)
    (hH : AffineAndRotationHolomorphy)
    (hh : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (ht : Analysis.ZerosOfAnalyticMapsAndThinSets)
    (hmul : LabelLinearity.Holds)
    (hkern : PlaneKernelProps.Holds)
    (hinv : MomentSymmetry.ReductionHolds)
    (hdens : DensityUniqueness.Claim) (hq : 1 ≤ q)
    (υ υ' : rightAngleMultiples) (ς ς' : Equiv.Perm (Fin (q + 1)))
    (φ : Fin (q + 1) → realLabels) : AgreeOnOverlaps S υ υ' ς ς' φ := by
  have hfr : ∀ (υ : rightAngleMultiples) (ς : Equiv.Perm (Fin (q + 1))),
      HolomorphicOnTuples (orderedTube υ ς)
        (fun z => orderedFrameKernel S υ ς z φ) := fun υ ς =>
    orderedFrameKernel_holomorphic hH hh hq ((hkern m S d q hq (permuteTuple ς φ)).2.2.2.2.2 υ)
  have hst₁ := orderedTube_stableOpenCone hL hF υ ς
  have hst₂ := orderedTube_stableOpenCone hL hF υ' ς'
  have hDo : IsOpen (orderedTube υ ς ∩ orderedTube υ' ς') :=
    hst₁.1.inter hst₂.1
  have hg := holomorphicOnTuples_sub
    (holomorphicOnTuples_of_locally hDo (fun a ha => ⟨_, _, ha.1, hfr υ ς, fun _ _ => rfl⟩) :
      HolomorphicOnTuples (orderedTube υ ς ∩ orderedTube υ' ς')
        (fun z => orderedFrameKernel S υ ς z φ))
    (holomorphicOnTuples_of_locally hDo (fun a ha => ⟨_, _, ha.2, hfr υ' ς', fun _ _ => rfl⟩) :
      HolomorphicOnTuples (orderedTube υ ς ∩ orderedTube υ' ς')
        (fun z => orderedFrameKernel S υ' ς' z φ))
  let O : Set (Fin (q + 1) → RealPlane) :=
    embedPlaneTuple ⁻¹' (orderedTube υ ς ∩ orderedTube υ' ς')
  have hOo : IsOpen O := hDo.preimage continuous_embedPlaneTuple
  have hc : ∀ (υ₀ : rightAngleMultiples) (ς₀ : Equiv.Perm (Fin (q + 1))),
      O ⊆ embedPlaneTuple ⁻¹' orderedTube υ₀ ς₀ →
      ContinuousOn (fun y => orderedFrameKernel S υ₀ ς₀ (embedPlaneTuple y) φ) O :=
    fun υ₀ ς₀ h => (continuousOn_of_holomorphicOnTuples (hfr υ₀ ς₀)).comp
      continuous_embedPlaneTuple.continuousOn h
  have hc₁ := hc υ ς fun _ h => h.1
  have hc₂ := hc υ' ς' fun _ h => h.2
  have hI : ∀ (υ₀ : rightAngleMultiples) (ς₀ : Equiv.Perm (Fin (q + 1))),
      O ⊆ embedPlaneTuple ⁻¹' orderedTube υ₀ ς₀ →
      ∀ α : Fin (q + 1) → RealPlane → ℂ, (∀ i, α i ∈ complexProfiles) →
      (∀ y : Fin (q + 1) → RealPlane, (∀ i, y i ∈ tsupport (α i)) → y ∈ O) →
      (∀ i, α i ≠ 0) → centeredFnAtProducts S α φ =
        profileIntegral α
          (fun y => orderedFrameKernel S υ₀ ς₀ (embedPlaneTuple y) φ) := by
    intro υ₀ ς₀ hsub α hα hs hne
    have hpl := integralRepresentation_holds d hF hmul hkern hinv hq υ₀ ς₀ φ α hα
      (fun y hy => hsub (hs y hy))
    exact (hpl.2 (hpl.1 hne)).2
  have hzero := (hdens (q + 1) (by omega) O hOo _ (hc₁.sub hc₂)).1
    (fun α hα => weightedIntegral_sub_eq_zero hc₁ hc₂ (hI υ ς fun _ h => h.1)
      (hI υ' ς' fun _ h => h.2) α hα)
  have hconv : Convex ℝ (orderedTube υ ς ∩ orderedTube υ' ς') :=
    hst₁.2.1.inter hst₂.2.1
  have hre : ∀ z ∈ orderedTube υ ς ∩ orderedTube υ' ς',
      embedPlaneTuple (tupleRe z) ∈ orderedTube υ ς ∩ orderedTube υ' ς' :=
    fun z hz => ⟨(hst₁.2.2.2 z hz.1).2.2, (hst₂.2.2.2 z hz.2).2.2⟩
  intro z hz
  exact sub_eq_zero.1 (eq_zero_of_eq_zero_on_real (ht ((q + 1) * 2) (by omega)).1 hDo hconv hre hg
    (fun y hy => hzero y hy) z hz)
theorem exists_extendsOrderedKernels {S : ConnFamily} {φ : Fin (q + 1) → realLabels}
    (hagree : ∀ (υ υ' : rightAngleMultiples) (ς ς' : Equiv.Perm (Fin (q + 1))),
      AgreeOnOverlaps S υ υ' ς ς' φ) :
    ∃ K, ExtendsOrderedKernels S φ K := by
  classical
  refine ⟨fun z => if h : ∃ p : rightAngleMultiples × Equiv.Perm (Fin (q + 1)),
      z ∈ orderedTube p.1 p.2 then
      orderedFrameKernel S h.choose.1 h.choose.2 z φ else 0, ?_⟩
  intro υ ς z hz
  have h : ∃ p : rightAngleMultiples × Equiv.Perm (Fin (q + 1)),
      z ∈ orderedTube p.1 p.2 := ⟨(υ, ς), hz⟩
  simp only [dif_pos h]
  exact hagree _ _ _ _ z ⟨h.choose_spec, hz⟩
theorem unionKernel_extends {S : ConnFamily} {φ : Fin (q + 1) → realLabels}
    (hagree : ∀ (υ υ' : rightAngleMultiples) (ς ς' : Equiv.Perm (Fin (q + 1))),
      AgreeOnOverlaps S υ υ' ς ς' φ) :
    ExtendsOrderedKernels S φ (unionKernel S φ) :=
  Classical.epsilon_spec (exists_extendsOrderedKernels hagree)
theorem mem_orderedTubeUnion_iff {z : Fin (q + 1) → ℂ × ℂ} :
    z ∈ orderedTubeUnion q ↔
      ∃ (υ : rightAngleMultiples) (ς : Equiv.Perm (Fin (q + 1))), z ∈ orderedTube υ ς := by
  simp [orderedTubeUnion]
theorem permuteTuple_update {α : Type*} (ς : Equiv.Perm (Fin (q + 1)))
    (φ : Fin (q + 1) → α) (j : Fin (q + 1)) (x : α) :
    permuteTuple ς (Function.update φ j x) =
      Function.update (permuteTuple ς φ) (ς.symm j) x := by
  funext i
  by_cases h : i = ς.symm j
  · subst h
    simp [permuteTuple]
  · have h' : ς i ≠ j := fun e => h (by simp [← e])
    simp [permuteTuple, Function.update_of_ne h, Function.update_of_ne h']
theorem uniqueExtension_holds {m : SharpScale} {S : ConnFamily}
    (d : PlaneDataWithAperture m S)
    (hF : TubeAndRotatedTubeRules)
    (hH : AffineAndRotationHolomorphy)
    (hh : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hmul : LabelLinearity.Holds)
    (hkern : PlaneKernelProps.Holds) (hq : 1 ≤ q)
    (hagree : ∀ (φ : Fin (q + 1) → realLabels) (υ υ' : rightAngleMultiples)
      (ς ς' : Equiv.Perm (Fin (q + 1))), AgreeOnOverlaps S υ υ' ς ς' φ)
    (φ : Fin (q + 1) → realLabels) : UniqueExtension S φ := by
  have hspec := fun ψ => unionKernel_extends (S := S) (φ := ψ) (hagree ψ)
  have hopen : IsOpen (orderedTubeUnion q) :=
    isOpen_iUnion fun υ => isOpen_iUnion fun ς => isOpen_orderedTube hF υ ς
  refine ⟨hspec φ, ?_, hopen, ?_, ?_⟩
  · intro K hK z hz
    obtain ⟨υ, ς, hz'⟩ := mem_orderedTubeUnion_iff.1 hz
    rw [hK υ ς z hz', hspec φ υ ς z hz']
  · refine holomorphicOnTuples_of_locally hopen fun a ha => ?_
    obtain ⟨υ, ς, ha'⟩ := mem_orderedTubeUnion_iff.1 ha
    exact ⟨_, _, ha', orderedFrameKernel_holomorphic hH hh hq
      ((hkern m S d q hq (permuteTuple ς φ)).2.2.2.2.2 υ), hspec φ υ ς⟩
  · intro z hz
    obtain ⟨υ, ς, hz'⟩ := mem_orderedTubeUnion_iff.1 hz
    have hval : ∀ ψ : Fin (q + 1) → realLabels, unionKernel S ψ z =
        planeKernel S (permuteTuple ς ψ) (unrotate υ
          (complexDifferences (permuteTuple ς z))) :=
      fun ψ => hspec ψ υ ς z hz'
    have hv : unrotate υ (complexDifferences (permuteTuple ς z)) ∈ forwardTubePow q :=
      ((hkern m S d q hq (permuteTuple ς φ)).2.2.2.2.2 υ).1 _
        ((mem_orderedTube_iff υ ς z).1 hz')
    intro φ' j a a' ψ ψ'
    simp only [hval, permuteTuple_update]
    have h := (hmul m S d q hq (Function.update (permuteTuple ς φ') (ς.symm j) ψ) (ς.symm j)
      ψ' a a').2 _ hv
    simpa only [Function.update_self, Function.update_idem] using h
theorem permuteTuple_mem_orderedTubeUnion (ς : Equiv.Perm (Fin (q + 1))) {z : Fin (q + 1) → ℂ × ℂ}
    (hz : z ∈ orderedTubeUnion q) :
    permuteTuple ς z ∈ orderedTubeUnion q := by
  obtain ⟨υ, ς', hz'⟩ := mem_orderedTubeUnion_iff.1 hz
  refine mem_orderedTubeUnion_iff.2 ⟨υ, ς⁻¹ * ς', ?_⟩
  show z ∈ orderedTube υ (ς * (ς⁻¹ * ς'))
  rwa [mul_inv_cancel_left]
theorem permuteTuple_permuteTuple_inv {α : Type*} (ς : Equiv.Perm (Fin (q + 1)))
    (z : Fin (q + 1) → α) : permuteTuple ς (permuteTuple ς⁻¹ z) = z := by
  funext i
  simp [permuteTuple]
theorem addConstTuple_addConstTuple_neg (z : Fin (q + 1) → ℂ × ℂ) (u : ℂ × ℂ) :
    addConstTuple (addConstTuple z (-u)) u = z := by
  funext i
  simp [addConstTuple]
theorem imagBoostTuple_imagBoostTuple_neg (hL : LightConeAndComplexRotationRules) (s : ℝ)
    (z : Fin (q + 1) → ℂ × ℂ) :
    imagBoostTuple s (imagBoostTuple (-s) z) = z := by
  funext i
  have h := (hL.2.2.2.2.1 (I * (s : ℂ))).2.2.2 (z i)
  have he : I * ((-s : ℝ) : ℂ) = -(I * (s : ℂ)) := by
    push_cast
    ring
  show complexBoost (I * (s : ℂ)) (complexBoost (I * ((-s : ℝ) : ℂ)) (z i)) = z i
  rw [he]
  exact h
theorem invariance_holds {S : ConnFamily} (hL : LightConeAndComplexRotationRules)
    (hF : TubeAndRotatedTubeRules)
    (hagree : ∀ (φ : Fin (q + 1) → realLabels) (υ υ' : rightAngleMultiples)
      (ς ς' : Equiv.Perm (Fin (q + 1))), AgreeOnOverlaps S υ υ' ς ς' φ)
    (ς : Equiv.Perm (Fin (q + 1))) (φ : Fin (q + 1) → realLabels) :
    Invariance S ς φ := by
  have hspec := fun ψ => unionKernel_extends (S := S) (φ := ψ) (hagree ψ)
  have hshift : ∀ (u : ℂ × ℂ) {z : Fin (q + 1) → ℂ × ℂ},
      z ∈ orderedTubeUnion q →
      addConstTuple z u ∈ orderedTubeUnion q := by
    intro u z hz
    obtain ⟨υ, ς', hz'⟩ := mem_orderedTubeUnion_iff.1 hz
    exact mem_orderedTubeUnion_iff.2
      ⟨υ, ς', ((orderedTube_stableOpenCone hL hF υ ς').2.2.2 z hz').1 u⟩
  have hrot : ∀ (s : ℝ) {z : Fin (q + 1) → ℂ × ℂ},
      z ∈ orderedTubeUnion q →
      imagBoostTuple s z ∈ orderedTubeUnion q := by
    intro s z hz
    obtain ⟨υ, ς', hz'⟩ := mem_orderedTubeUnion_iff.1 hz
    exact mem_orderedTubeUnion_iff.2
      ⟨υ, ς', ((orderedTube_stableOpenCone hL hF υ ς').2.2.2 z hz').2.1 s⟩
  refine ⟨?_, fun u => ?_, fun s => ?_, fun z hz => ⟨?_, fun u => ?_⟩⟩
  · ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact permuteTuple_mem_orderedTubeUnion ς hw
    · intro hz
      exact ⟨_, permuteTuple_mem_orderedTubeUnion ς⁻¹ hz, permuteTuple_permuteTuple_inv ς z⟩
  · ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hshift u hw
    · intro hz
      exact ⟨_, hshift (-u) hz, addConstTuple_addConstTuple_neg z u⟩
  · ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hrot s hw
    · intro hz
      exact ⟨_, hrot (-s) hz, imagBoostTuple_imagBoostTuple_neg hL s z⟩
  · obtain ⟨υ, ς', hz'⟩ := mem_orderedTubeUnion_iff.1 hz
    have h1 : permuteTuple ς z ∈ orderedTube υ (ς⁻¹ * ς') := by
      show z ∈ orderedTube υ (ς * (ς⁻¹ * ς'))
      rwa [mul_inv_cancel_left]
    rw [hspec _ υ _ _ h1, hspec φ υ ς' z hz']
    show orderedFrameKernel S υ (ς * (ς⁻¹ * ς')) z φ = _
    rw [mul_inv_cancel_left]
  · obtain ⟨υ, ς', hz'⟩ := mem_orderedTubeUnion_iff.1 hz
    have h1 := ((orderedTube_stableOpenCone hL hF υ ς').2.2.2 z hz').1 u
    rw [hspec φ υ ς' _ h1, hspec φ υ ς' z hz']
    have he : complexDifferences (permuteTuple ς' (addConstTuple z u)) =
        complexDifferences (permuteTuple ς' z) := by
      funext i
      simp [complexDifferences, permuteTuple, addConstTuple]
    unfold orderedFrameKernel
    rw [he]
theorem inner_unitX (y : RealPlane) : inner ℝ unitX y = y 0 := by
  rw [inner_eq_coord_sum]
  simp [unitX]
theorem inner_unitY (y : RealPlane) : inner ℝ unitY y = y 1 := by
  rw [inner_eq_coord_sum]
  simp [unitY]
theorem rotatedDirection_apply_zero (υ : rightAngleMultiples) :
    rotatedDirection υ 0 = Real.cos υ := by
  simp [rotatedDirection, rotatedUnitVector_eq_cos_sin, Complex.cos_ofReal_re]
theorem rotatedDirection_apply_one (υ : rightAngleMultiples) :
    rotatedDirection υ 1 = Real.sin υ := by
  simp [rotatedDirection, rotatedUnitVector_eq_cos_sin, Complex.sin_ofReal_re]
theorem sin_eq_zero_or_cos_eq_zero (υ : rightAngleMultiples) :
    Real.sin υ = 0 ∨ Real.cos υ = 0 := by
  obtain ⟨k, hk⟩ := υ.2
  have h : Real.sin (2 * (υ : ℝ)) = 0 := by
    rw [hk, show 2 * ((k : ℝ) * (Real.pi / 2)) = (k : ℝ) * Real.pi by ring]
    exact Real.sin_int_mul_pi k
  rw [Real.sin_two_mul] at h
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (by simpa using h)
  · exact Or.inr h
theorem not_injective_iff_exists_ne_eq {n : ℕ} (f : Fin n → ℝ) :
    ¬ Function.Injective f ↔ ∃ i j, i ≠ j ∧ f i = f j := by
  rw [Function.not_injective_iff]
  exact ⟨fun ⟨a, b, h, hn⟩ => ⟨a, b, hn, h⟩, fun ⟨a, b, hn, h⟩ => ⟨a, b, h, hn⟩⟩
theorem exists_lt_eq_of_not_injective {n : ℕ} {f : Fin n → ℝ} (h : ¬ Function.Injective f) :
    ∃ i j, i < j ∧ f i = f j := by
  obtain ⟨a, b, hn, he⟩ := (not_injective_iff_exists_ne_eq f).1 h
  rcases lt_or_gt_of_ne hn with hl | hl
  · exact ⟨a, b, hl, he⟩
  · exact ⟨b, a, hl, he.symm⟩
theorem embedPlaneTuple_mem_orderedTubeUnion_of_injective (hF : TubeAndRotatedTubeRules)
    (υ : rightAngleMultiples) {y : Fin (q + 1) → RealPlane}
    (h : Function.Injective fun i => inner ℝ (rotatedDirection υ) (y i)) :
    embedPlaneTuple y ∈ orderedTubeUnion q := by
  let f : Fin (q + 1) → ℝ := fun i => inner ℝ (rotatedDirection υ) (y i)
  have hmono : Monotone (f ∘ Tuple.sort f) := Tuple.monotone_sort f
  have hstrict : StrictMono (f ∘ Tuple.sort f) :=
    hmono.strictMono_of_injective (h.comp (Tuple.sort f).injective)
  exact mem_orderedTubeUnion_iff.2 ⟨υ, Tuple.sort f,
    (embedPlaneTuple_mem_orderedTube_iff hF υ _ y).2 fun i =>
      hstrict (Fin.castSucc_lt_succ (i := i))⟩
theorem orderedRealTuples_eq (hF : TubeAndRotatedTubeRules) :
    orderedRealTuples q =
      {y | Function.Injective (fun i => y i 0) ∨ Function.Injective (fun i => y i 1)} := by
  ext y
  constructor
  · intro hy
    obtain ⟨υ, ς, hz⟩ := mem_orderedTubeUnion_iff.1 hy
    have hs := (strictMono_of_embedPlaneTuple_mem hF hz).injective
    have hinj : ∀ a b : Fin (q + 1),
        inner ℝ (rotatedDirection υ) (y a) = inner ℝ (rotatedDirection υ) (y b) → a = b := by
      intro a b h
      apply ς.symm.injective
      apply hs
      simpa using h
    rcases sin_eq_zero_or_cos_eq_zero υ with h0 | h0
    · left
      intro a b h
      apply hinj
      simp only at h
      rw [inner_eq_coord_sum, inner_eq_coord_sum, rotatedDirection_apply_one, h0]
      simp [h]
    · right
      intro a b h
      apply hinj
      simp only at h
      rw [inner_eq_coord_sum, inner_eq_coord_sum, rotatedDirection_apply_zero, h0]
      simp [h]
  · rintro (h | h)
    · refine embedPlaneTuple_mem_orderedTubeUnion_of_injective hF rightAngleZero ?_
      simpa only [rotatedDirection_rightAngleZero, inner_unitX] using h
    · refine embedPlaneTuple_mem_orderedTubeUnion_of_injective hF rightAngle ?_
      simpa only [rotatedDirection_rightAngle, inner_unitY] using h
theorem compl_orderedRealTuples_eq (hF : TubeAndRotatedTubeRules) :
    (orderedRealTuples q)ᶜ =
      ⋃ (i : Fin (q + 1)) (j : Fin (q + 1)) (_ : i < j) (k : Fin (q + 1)) (l : Fin (q + 1))
        (_ : k < l), (coincidenceSubspace i j k l : Set (Fin (q + 1) → RealPlane)) := by
  rw [orderedRealTuples_eq hF]
  ext y
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_or, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨i, j, hij, e₁⟩ := exists_lt_eq_of_not_injective h₁
    obtain ⟨k, l, hkl, e₂⟩ := exists_lt_eq_of_not_injective h₂
    exact ⟨i, j, hij, k, l, hkl, e₁, e₂⟩
  · rintro ⟨i, j, hij, k, l, hkl, e₁, e₂⟩
    exact ⟨fun h => hij.ne (h e₁), fun h => hkl.ne (h e₂)⟩
theorem finrank_quotient_coincidenceSubspace {i j k l : Fin (q + 1)} (hij : i < j) (hkl : k < l) :
    Module.finrank ℝ ((Fin (q + 1) → RealPlane) ⧸ coincidenceSubspace i j k l) = 2 := by
  let T : (Fin (q + 1) → RealPlane) →ₗ[ℝ] ℝ × ℝ :=
    { toFun := fun y => (y i 0 - y j 0, y k 1 - y l 1)
      map_add' := by
        intro a b
        ext <;> simp <;> ring
      map_smul' := by
        intro c a
        ext <;> simp <;> ring }
  have hker : LinearMap.ker T = coincidenceSubspace i j k l := by
    ext y
    simp only [LinearMap.mem_ker]
    show (y i 0 - y j 0, y k 1 - y l 1) = 0 ↔ y i 0 = y j 0 ∧ y k 1 = y l 1
    simp [Prod.ext_iff, sub_eq_zero]
  have hsurj : Function.Surjective T := by
    rintro ⟨a, b⟩
    refine ⟨fun m => !₂[if m = i then a else 0, if m = k then b else 0], ?_⟩
    show (_ - _, _ - _) = (a, b)
    simp [hij.ne', hkl.ne']
  rw [← hker, (T.quotKerEquivOfSurjective hsurj).finrank_eq]
  simp
abbrev CoincidenceIndex (q : ℕ) : Type :=
  {t : Fin (q + 1) × Fin (q + 1) × Fin (q + 1) × Fin (q + 1) //
    t.1 < t.2.1 ∧ t.2.2.1 < t.2.2.2}
theorem orderedRealTuples_isOpen_dense_connected (hF : TubeAndRotatedTubeRules)
    (ht : Analysis.ComplementOfCodimTwoSubspaces ((q + 1) * 2))
    (hq : 1 ≤ q) :
    IsOpen (orderedRealTuples q) ∧ Dense (orderedRealTuples q) ∧
      IsConnected (orderedRealTuples q) := by
  have hfin : Module.finrank ℝ (Fin (q + 1) → RealPlane) = (q + 1) * 2 := by
    rw [Module.finrank_pi_fintype]
    simp
  obtain ⟨e⟩ : Nonempty ((Fin (q + 1) → RealPlane) ≃L[ℝ] (Fin ((q + 1) * 2) → ℝ)) :=
    ⟨ContinuousLinearEquiv.ofFinrankEq (by rw [hfin]; simp)⟩
  let eL := e.toLinearEquiv
  let W : CoincidenceIndex q → Submodule ℝ (Fin (q + 1) → RealPlane) :=
    fun t => coincidenceSubspace t.1.1 t.1.2.1 t.1.2.2.1 t.1.2.2.2
  obtain ⟨en⟩ : Nonempty (CoincidenceIndex q ≃ Fin (Fintype.card (CoincidenceIndex q))) :=
    ⟨Fintype.equivFin _⟩
  let V : Fin (Fintype.card (CoincidenceIndex q)) → AffineSubspace ℝ (Fin ((q + 1) * 2) → ℝ) :=
    fun c => AffineSubspace.mk' 0 ((W (en.symm c)).map eL.toLinearMap)
  have hp : 1 ≤ Fintype.card (CoincidenceIndex q) := by
    have hne : Nonempty (CoincidenceIndex q) :=
      ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩),
        Fin.mk_lt_mk.2 Nat.zero_lt_one, Fin.mk_lt_mk.2 Nat.zero_lt_one⟩⟩
    exact Fintype.card_pos
  have hdim : ∀ c, Module.finrank ℝ (V c).direction + 2 ≤ (q + 1) * 2 := by
    intro c
    have h1 : (V c).direction = (W (en.symm c)).map eL.toLinearMap :=
      AffineSubspace.direction_mk' _ _
    have h2 : Module.finrank ℝ ((W (en.symm c)).map eL.toLinearMap) =
        Module.finrank ℝ (W (en.symm c)) :=
      LinearEquiv.finrank_map_eq eL _
    have h3 := Submodule.finrank_quotient_add_finrank (W (en.symm c))
    have h4 := finrank_quotient_coincidenceSubspace (en.symm c).2.1 (en.symm c).2.2
    have h4' : Module.finrank ℝ ((Fin (q + 1) → RealPlane) ⧸ W (en.symm c)) = 2 := h4
    rw [h1, h2]
    omega
  obtain ⟨ho, hd, hc⟩ := ht (by omega) (Fintype.card (CoincidenceIndex q)) hp V
    (fun c => ⟨0, AffineSubspace.self_mem_mk' _ _⟩) hdim
  have hmem : ∀ y, y ∈ orderedRealTuples q ↔
      e y ∈ (⋃ c, (V c : Set (Fin ((q + 1) * 2) → ℝ)))ᶜ := by
    intro y
    rw [← not_iff_not, Set.mem_compl_iff, not_not,
      ← Set.mem_compl_iff (s := orderedRealTuples q), compl_orderedRealTuples_eq hF]
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨i, j, hij, k, l, hkl, hy⟩
      refine ⟨en ⟨(i, j, k, l), hij, hkl⟩, ?_⟩
      show e y ∈ AffineSubspace.mk' 0 _
      rw [AffineSubspace.mem_mk']
      simp only [vsub_eq_sub, sub_zero, Equiv.symm_apply_apply]
      exact ⟨y, hy, rfl⟩
    · rintro ⟨c, hc'⟩
      have hc'' : e y ∈ AffineSubspace.mk' 0 ((W (en.symm c)).map eL.toLinearMap) := hc'
      rw [AffineSubspace.mem_mk'] at hc''
      simp only [vsub_eq_sub, sub_zero] at hc''
      obtain ⟨y', hy', he⟩ := hc''
      have hyy : y' = y := e.injective he
      subst hyy
      exact ⟨_, _, (en.symm c).2.1, _, _, (en.symm c).2.2, hy'⟩
  have hpre : orderedRealTuples q = e ⁻¹' (⋃ c, (V c : Set (Fin ((q + 1) * 2) → ℝ)))ᶜ :=
    Set.ext hmem
  have himg : orderedRealTuples q =
      e.symm '' (⋃ c, (V c : Set (Fin ((q + 1) * 2) → ℝ)))ᶜ := by
    ext y
    constructor
    · intro hy
      exact ⟨e y, (hmem y).1 hy, e.symm_apply_apply y⟩
    · rintro ⟨x, hx, rfl⟩
      refine (hmem _).2 ?_
      simpa using hx
  refine ⟨?_, ?_, ?_⟩
  · rw [hpre]
    exact ho.preimage e.continuous
  · rw [hpre]
    exact hd.preimage e.toHomeomorph.isOpenMap
  · rw [himg]
    exact hc.image _ e.symm.continuous.continuousOn
theorem injective_add_const_iff {n : ℕ} (f : Fin n → ℝ) (c : ℝ) :
    Function.Injective (fun i => f i + c) ↔ Function.Injective f :=
  ⟨fun h a b e => h (by simp [e]), fun h a b e => h (by simpa using e)⟩
theorem orderedTuplesCharacterization_holds (hF : TubeAndRotatedTubeRules)
    (hS : SectorAndPencilRules)
    (ht : Analysis.ComplementOfCodimTwoSubspaces ((q + 1) * 2))
    (hq : 1 ≤ q) (φ₀ : openingAngles) : OrderedTuplesCharacterization φ₀ q := by
  have hord := orderedRealTuples_eq (q := q) hF
  have hmem : ∀ y : Fin (q + 1) → RealPlane, y ∈ orderedRealTuples q ↔
      Function.Injective (fun i => y i 0) ∨ Function.Injective (fun i => y i 1) := fun y => by
    rw [hord]
    rfl
  obtain ⟨ho, hd, hc⟩ := orderedRealTuples_isOpen_dense_connected hF ht hq
  have hpen : pencilSet φ₀ (q + 1) ⊆ embedPlaneTuple ⁻¹' orderedTube rightAngleZero 1 := by
    intro y hy
    refine (embedPlaneTuple_mem_orderedTube_iff hF rightAngleZero 1 y).2 fun i => ?_
    have h : 0 < (y i.succ - y i.castSucc) 0 := (hS φ₀).2.2.1 (hy i)
    rw [rotatedDirection_rightAngleZero, inner_unitX, inner_unitX]
    simp only [PiLp.sub_apply] at h
    simpa using (sub_pos.1 h)
  refine ⟨hord, compl_orderedRealTuples_eq hF,
    fun i j k l hij hkl => finrank_quotient_coincidenceSubspace hij hkl, ?_, ?_,
    ?_, ?_, ho, hd, hc, ?_, ?_, hpen, ?_⟩
  · intro y i j hij he hy
    rcases (hmem y).1 hy with h | h
    · exact hij (h (by simp only [he]))
    · exact hij (h (by simp only [he]))
  · intro y hy a b hab
    rcases (hmem y).1 hy with h | h
    · exact h (by simp only [hab])
    · exact h (by simp only [hab])
  · intro y _
    rw [hmem, not_or]
    exact and_congr (not_injective_iff_exists_ne_eq _) (not_injective_iff_exists_ne_eq _)
  · intro y _ hn υ ς h
    exact hn (mem_orderedTubeUnion_iff.2 ⟨υ, ς, h⟩)
  · intro ς y
    rw [hmem, hmem]
    exact or_congr (ς.injective_comp fun i => y i 0).symm (ς.injective_comp fun i => y i 1).symm
  · intro u y
    rw [hmem, hmem]
    exact or_congr (injective_add_const_iff (fun i => y i 0) (u 0)).symm
      (injective_add_const_iff (fun i => y i 1) (u 1)).symm
  · intro y hy
    exact mem_orderedTubeUnion_iff.2 ⟨rightAngleZero, 1, hpen hy⟩
theorem holds_of_rules (hrules : ForwardTube.RotationRules.Holds)
    (htools : Analysis.ZerosOfAnalyticMapsAndThinSets)
    (hmul : LabelLinearity.Holds)
    (hkern : PlaneKernelProps.Holds)
    (hinv : MomentSymmetry.ReductionHolds)
    (hh : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hdens : DensityUniqueness.Claim) : Holds := by
  obtain ⟨hL, -, -, hH, hF, hS⟩ := hrules
  intro m S d q hq φ υ υ' ς ς'
  have hagree : ∀ (ψ : Fin (q + 1) → realLabels) (a b : rightAngleMultiples)
      (c e : Equiv.Perm (Fin (q + 1))), AgreeOnOverlaps S a b c e ψ :=
    fun ψ a b c e => agreeOnOverlaps_holds d hL hF hH hh htools hmul hkern hinv hdens hq a b c e ψ
  exact ⟨orderedFrameKernel_holomorphic hH hh hq
      ((hkern m S d q hq (permuteTuple ς φ)).2.2.2.2.2 υ),
    orderedTube_stableOpenCone hL hF υ ς, realLocusOrdered_holds hF υ ς,
    integralRepresentation_holds d hF hmul hkern hinv hq υ ς φ, hagree φ υ υ' ς ς',
    uniqueExtension_holds d hF hH hh hmul hkern hq hagree φ,
    invariance_holds hL hF hagree ς φ,
    orderedTuplesCharacterization_holds hF hS ((htools ((q + 1) * 2) (by omega)).2.2.2) hq
      d.angle⟩
end EuclideanFunctionals.UnionKernel
end YangMills.Construction
end
