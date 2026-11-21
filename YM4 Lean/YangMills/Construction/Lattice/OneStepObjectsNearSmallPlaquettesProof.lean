import YangMills.Construction.Lattice.AveragingMapIsABorelMapProof
import YangMills.Construction.Lattice.CombGaugeOfABoxProof
import YangMills.Construction.Lattice.DoubleBlockFromItsLowestCorner
import YangMills.Construction.Lattice.GaugeCovarianceOfTheOneStepObjects
import YangMills.Construction.Lattice.HolomorphyOfBoundedOneStepObjectsProof
import YangMills.Construction.Lattice.OneStepObjectsNearSmallPlaquettes
import YangMills.Construction.Lattice.PathsOfBlocksAndDoubleBlocks
import YangMills.Construction.Matrices.ImplicitFunctionOnTheRealFormProof
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices Coordinates Conventions Averaging
namespace PeriodicLattice
namespace StepObjectsNearSmallCurvatureProof
private theorem mem_unitaryGroup_of_mem {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    g ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hg).1
private theorem inv_mul_self_of {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    g⁻¹ * g = 1 := by apply _root_.YangMills.SharedProofs.p1227 <;> assumption
private theorem inv_inv_of {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    (g⁻¹)⁻¹ = g := by apply _root_.YangMills.SharedProofs.p318 <;> assumption
private theorem inv_mem_specialUnitary {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) : g⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
private theorem det_eq_one {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    g.det = 1 :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hg).2
private theorem operatorNorm_sub_one_le_two {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) : ComplexMatrix2.operatorNorm (g - 1) ≤ 2 := by
  have h₁ : ‖g‖ = 1 := CStarRing.norm_of_mem_unitary (mem_unitaryGroup_of_mem hg)
  have h₂ : ‖(1 : ComplexMatrix2)‖ = 1 := CStarRing.norm_one
  calc ComplexMatrix2.operatorNorm (g - 1) ≤ ‖g‖ + ‖(1 : ComplexMatrix2)‖ := norm_sub_le _ _
    _ = 2 := by rw [h₁, h₂]; norm_num
section Holomorphy
open Matrices.GroupLieProduct
variable {σ τ : Type}
private theorem operatorNorm_le_supNorm [Finite σ] (A : σ → ComplexMatrix2) (i : σ) :
    ComplexMatrix2.operatorNorm (A i) ≤ supNorm A :=
  le_ciSup (f := fun i => ComplexMatrix2.operatorNorm (A i)) (Set.finite_range _).bddAbove i
private theorem supNorm_nonneg (A : σ → ComplexMatrix2) : 0 ≤ supNorm A :=
  Real.iSup_nonneg fun _ => norm_nonneg _
private theorem supNorm_le {A : σ → ComplexMatrix2} {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ i, ComplexMatrix2.operatorNorm (A i) ≤ t) : supNorm A ≤ t :=
  Real.iSup_le h ht
private theorem isSupOpen_supBall [Finite σ] (ρ : ℝ) : IsSupOpen (supBall σ ρ) := by
  refine ⟨fun A hA => hA.1, fun A hA => ⟨ρ - supNorm A, sub_pos.2 hA.2, fun B hB hd => ⟨hB, ?_⟩⟩⟩
  have h : supNorm B ≤ supNorm A + supNorm (B - A) := by
    refine supNorm_le (add_nonneg (supNorm_nonneg _) (supNorm_nonneg _)) fun i => ?_
    have hi : B i = A i + (B - A) i := by simp
    calc ComplexMatrix2.operatorNorm (B i) = ‖A i + (B - A) i‖ := by rw [← hi]
      _ ≤ ‖A i‖ + ‖(B - A) i‖ := norm_add_le _ _
      _ ≤ supNorm A + supNorm (B - A) :=
        add_le_add (operatorNorm_le_supNorm A i) (operatorNorm_le_supNorm (B - A) i)
  linarith
private theorem isHolomorphicIn_iff
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) {N N' : ℕ}
    {O : Set (ComplexCoordinates N)} {f : ComplexCoordinates N → ComplexCoordinates N'} :
    ComplexCoordinates.IsHolomorphicIn O f ↔ IsOpen O ∧ DifferentiableOn ℂ f O := by apply _root_.YangMills.SharedProofs.p123 <;> assumption
private def entryEquiv : ComplexMatrix2 ≃ₗ[ℂ] ComplexCoordinates 4 :=
  { ComplexCoordinates.matrixEquiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
private def tracelessProjection : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2.traceless :=
  LinearMap.codRestrict ComplexMatrix2.traceless
    (LinearMap.id - (Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight ((1 / 2 : ℂ) • (1 : ComplexMatrix2)))
    (by
      intro X
      change Matrix.trace _ = 0
      simp [Matrix.trace_fin_two])
private theorem tracelessProjection_of_mem (A : ComplexMatrix2) (hA : A ∈ ComplexMatrix2.traceless) :
    tracelessProjection A = ⟨A, hA⟩ := by
  apply Subtype.ext
  have h : Matrix.trace A = 0 := hA
  simp [tracelessProjection, h]
private def basisCoord (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) :
    ComplexMatrix2 →ₗ[ℂ] Fin 3 → ℂ :=
  b.equivFun.toLinearMap ∘ₗ tracelessProjection
private theorem sum_basisCoord_smul (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (A : ComplexMatrix2) (hA : A ∈ ComplexMatrix2.traceless) :
    ∑ c, basisCoord b A c • (b c : ComplexMatrix2) = A := by
  have h : basisCoord b A = b.equivFun ⟨A, hA⟩ := by
    rw [basisCoord, LinearMap.comp_apply, tracelessProjection_of_mem A hA]
    rfl
  rw [h]
  calc ∑ c, b.equivFun ⟨A, hA⟩ c • (b c : ComplexMatrix2)
      = ((∑ c, b.equivFun ⟨A, hA⟩ c • b c : ComplexMatrix2.traceless) : ComplexMatrix2) := by
        simp only [Submodule.coe_sum, Submodule.coe_smul]
    _ = A := by rw [b.sum_equivFun]
private def familyCoords [Fintype τ] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : τ ≃ Fin (Fintype.card τ)) :
    (τ → ComplexMatrix2) →ₗ[ℂ] ComplexCoordinates (Fintype.card τ * 3) where
  toFun A k := basisCoord b (A (ν.symm (finProdFinEquiv.symm k).1)) (finProdFinEquiv.symm k).2
  map_add' A B := by
    funext k
    simp
  map_smul' t A := by
    funext k
    simp
private def familyOfCoordsLinear [Fintype σ] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) :
    ComplexCoordinates (Fintype.card σ * 3) →ₗ[ℂ] σ → ComplexMatrix2 where
  toFun := tupleOfCoords b ν
  map_add' w w' := by
    funext i
    simp [tupleOfCoords, ComplexCoordinates.tracelessTuple, add_smul, Finset.sum_add_distrib]
  map_smul' t w := by
    funext i
    simp [tupleOfCoords, ComplexCoordinates.tracelessTuple, mul_smul, Finset.smul_sum]
private theorem tupleOfCoords_familyCoords [Fintype τ]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : τ ≃ Fin (Fintype.card τ)) {A : τ → ComplexMatrix2} (hA : A ∈ tracelessPi τ) :
    tupleOfCoords b ν (familyCoords b ν A) = A := by
  funext i
  change ∑ c, familyCoords b ν A (finProdFinEquiv (ν i, c)) • (b c : ComplexMatrix2) = A i
  have h : ∀ c, familyCoords b ν A (finProdFinEquiv (ν i, c)) = basisCoord b (A i) c := by
    intro c
    change basisCoord b (A (ν.symm (finProdFinEquiv.symm (finProdFinEquiv (ν i, c))).1))
      (finProdFinEquiv.symm (finProdFinEquiv (ν i, c))).2 = _
    rw [Equiv.symm_apply_apply]
    simp
  simp only [h]
  exact sum_basisCoord_smul b (A i) (hA i)
private theorem tupleOfCoords_mem [Fintype σ] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ)) (w : ComplexCoordinates (Fintype.card σ * 3)) :
    tupleOfCoords b ν w ∈ tracelessPi σ := by apply _root_.YangMills.Construction.Matrices.GroupLieProduct.Subspaces.RealForm.tupleOfCoords_mem <;> assumption
private theorem isHolomorphicOnTraceless_comp_affine
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ExpChartHolomorphy.ExpChartTheory) [Fintype σ] [Fintype τ]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (Θ : (σ → ComplexMatrix2) →ₗ[ℂ] τ → ComplexMatrix2) {p₀ : τ → ComplexMatrix2}
    (hp₀ : p₀ ∈ tracelessPi τ) (hΘ : ∀ A ∈ tracelessPi σ, Θ A ∈ tracelessPi τ) {ρ r : ℝ}
    (hball : ∀ A ∈ supBall σ ρ, p₀ + Θ A ∈ supBall τ r) (T : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2)
    {F : (τ → ComplexMatrix2) → ComplexMatrix2} {G : (σ → ComplexMatrix2) → ComplexMatrix2}
    (hF : IsHolomorphicOnTraceless b ComplexCoordinates.matrixEquiv (supBall τ r) F)
    (hG : ∀ A ∈ supBall σ ρ, G A = T (F (p₀ + Θ A))) :
    IsHolomorphicOnTraceless b ComplexCoordinates.matrixEquiv (supBall σ ρ) G := by
  refine ⟨isSupOpen_supBall ρ, fun ν => ?_⟩
  have hopen : IsOpen (tupleOfCoords b ν ⁻¹' supBall σ ρ) :=
    (((hE.2.1 σ).1 _ fun A hA => hA.1).2 b ν).1 (isSupOpen_supBall ρ)
  let ν₂ : τ ≃ Fin (Fintype.card τ) := Fintype.equivFin τ
  have hf := ((isHolomorphicIn_iff hH).1 (hF.2 ν₂)).2
  let Λ : ComplexCoordinates (Fintype.card σ * 3) →ₗ[ℂ] ComplexCoordinates (Fintype.card τ * 3) :=
    familyCoords b ν₂ ∘ₗ Θ ∘ₗ familyOfCoordsLinear b ν
  let Ψ : ComplexCoordinates (Fintype.card σ * 3) → ComplexCoordinates (Fintype.card τ * 3) :=
    fun w => familyCoords b ν₂ p₀ + Λ w
  let T' : ComplexCoordinates 4 →ₗ[ℂ] ComplexCoordinates 4 :=
    entryEquiv.toLinearMap ∘ₗ T ∘ₗ entryEquiv.symm.toLinearMap
  have hΨ : ∀ w, tupleOfCoords b ν₂ (Ψ w) = p₀ + Θ (tupleOfCoords b ν w) := by
    intro w
    have hmem : p₀ + Θ (tupleOfCoords b ν w) ∈ tracelessPi τ := fun i =>
      Submodule.add_mem _ (hp₀ i) (hΘ _ (tupleOfCoords_mem b ν w) i)
    have h := tupleOfCoords_familyCoords b ν₂ hmem
    have hsum : Ψ w = familyCoords b ν₂ (p₀ + Θ (tupleOfCoords b ν w)) := by
      rw [map_add]
      rfl
    rw [hsum, h]
  have hdΨ : Differentiable ℂ Ψ :=
    (differentiable_const _).add (LinearMap.toContinuousLinearMap Λ).differentiable
  have hdT : Differentiable ℂ T' := (LinearMap.toContinuousLinearMap T').differentiable
  have hmaps : Set.MapsTo Ψ (tupleOfCoords b ν ⁻¹' supBall σ ρ)
      (tupleOfCoords b ν₂ ⁻¹' supBall τ r) := fun w hw => by
    change tupleOfCoords b ν₂ (Ψ w) ∈ supBall τ r
    rw [hΨ]
    exact hball _ hw
  have hcomp := hdT.comp_differentiableOn (hf.comp hdΨ.differentiableOn hmaps)
  refine (isHolomorphicIn_iff hH).2 ⟨hopen, hcomp.congr fun w hw => ?_⟩
  simp only [Function.comp_apply]
  rw [hG _ hw, hΨ]
  change ComplexCoordinates.matrixEquiv _ = entryEquiv (T (entryEquiv.symm (entryEquiv _)))
  rw [LinearEquiv.symm_apply_apply]
  rfl
end Holomorphy
section Locality
variable {L m K n : ℕ}
private theorem eq_source_or_target {c : BondAtLevel L m K (n + 1)} {y : SiteAtLevel L m K (n + 1)}
    (hy : y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1)))) :
    y = c.source ∨ y = c.target := by
  simpa using hy
private structure BlockRoutes (c : BondAtLevel L m K (n + 1)) (μ : Fin 4) : Prop where
  coords : DoubleBlockCoordinates (levelDepth K n) c μ
  axial : DoubleBlockAxialPaths (levelDepth K n) c μ
  paths : PathsInsideDoubleBlock (levelDepth K n) c
  source_mem : c.source.toSublattice (levelDepth K n) ∈ sitesInBlock (levelDepth K n) c.source
  anchor_mem : blockAnchor (levelDepth K n) c.source ∈ sitesInBlock (levelDepth K n) c.source
private theorem blockRoutes (h : BlockPaths.Statement)
    (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K) (c : BondAtLevel L m K (n + 1))
    {μ : Fin 4} (hμ : c.target - c.source = unitStep L m (levelDepth K (n + 1)) μ) :
    BlockRoutes c μ := by
  obtain ⟨hsite, hbond⟩ := h L m K hL.1 hL.2 hm n hn
  obtain ⟨hD, -, -, hS, hP⟩ := hbond c μ hμ
  have hB := (hsite c.source).1
  refine ⟨hD, hS, hP, ?_, hB.2.2⟩
  have h₁ : 1 ≤ L := by have := hL.2; omega
  have h₀ : (0 : ℤ) ≤ centreToFaceSteps L := by
    unfold centreToFaceSteps
    omega
  have hq : (0 : Fin 4 → ℤ) ∈ blockIndexBox L := fun ν => by
    simpa using h₀
  have hmem := Set.mem_image_of_mem
    (fun p => (offsetSite (c.source.toSublattice (levelDepth K n)) p : FourTorus L m)) hq
  rw [hB.1.2] at hmem
  change (c.source.toSublattice (levelDepth K n) : FourTorus L m) ∈ unitBlock c.source
  simpa [offsetSite] using hmem
variable {c : BondAtLevel L m K (n + 1)} {μ : Fin 4} {W W' : BondAtLevel L m K n → ComplexMatrix2}
private theorem pathHolonomy_congr {Γ : List (BondAtLevel L m K n)} (h : ∀ b ∈ Γ, W b = W' b) :
    pathHolonomy W Γ = pathHolonomy W' Γ := by
  unfold pathHolonomy
  rw [List.map_congr_left h]
private theorem contourHolonomies_congr (R : BlockRoutes c μ)
    (hE : Set.EqOn W W' (bondsInDoubleBlock c))
    {y : SiteAtLevel L m K (n + 1)} (hy : y = c.source ∨ y = c.target) {x : SiteAtLevel L m K n}
    (hx : x ∈ sitesInBlock (levelDepth K n) y) :
    contourHolonomies W y x = contourHolonomies W' y x :=
  funext fun σ => pathHolonomy_congr fun b hb => hE ((R.paths.1 y hy x hx).1 _ ⟨σ, rfl⟩ b hb)
private theorem contourHolonomy_congr (R : BlockRoutes c μ)
    (hE : Set.EqOn W W' (bondsInDoubleBlock c)) (s : AveragingScheme)
    {y : SiteAtLevel L m K (n + 1)} (hy : y = c.source ∨ y = c.target) {x : SiteAtLevel L m K n}
    (hx : x ∈ sitesInBlock (levelDepth K n) y) :
    contourHolonomy s W y x = contourHolonomy s W' y x := by
  cases s with
  | centred =>
    simp only [contourHolonomy, complexMeanContourHolonomy]
    rw [contourHolonomies_congr R hE hy hx]
  | cornered =>
    simp only [contourHolonomy]
    exact pathHolonomy_congr fun b hb => hE ((R.paths.1 y hy x hx).2 b hb)
private theorem bondsInside_subset {y : SiteAtLevel L m K (n + 1)}
    (hy : y = c.source ∨ y = c.target) :
    (bondsInside (unitBlock y) : Set (BondAtLevel L m K n)) ⊆ bondsInDoubleBlock c := by
  have hsub : unitBlock y ⊆ bondDoubleBlock c := by
    rcases hy with rfl | rfl
    · exact Set.subset_union_left
    · exact Set.subset_union_right
  exact fun b hb => ⟨hsub hb.1, hsub hb.2⟩
private theorem isGaugeField_congr {X : Set (FourTorus L m)}
    (hW : IsGaugeField complexGaugeGroup (bondsInside X) W)
    (hE : Set.EqOn W W' (bondsInside X)) :
    IsGaugeField complexGaugeGroup (bondsInside X) W' := by
  refine ⟨fun b hb => hE hb ▸ hW.1 b hb, fun b hb => ?_⟩
  have hr : b.opposite ∈ (bondsInside X : Set (BondAtLevel L m K n)) := ⟨hb.2, hb.1⟩
  rw [← hE hr, ← hE hb]
  exact hW.2 b hb
private theorem isContourHolonomyDefined_congr (R : BlockRoutes c μ)
    (hE : Set.EqOn W W' (bondsInDoubleBlock c))
    (s : AveragingScheme) {y : SiteAtLevel L m K (n + 1)} (hy : y = c.source ∨ y = c.target)
    {x : SiteAtLevel L m K n} (h : IsContourHolonomyDefined s W y x) :
    IsContourHolonomyDefined s W' y x := by
  obtain ⟨hx, hconf, hs⟩ := h
  refine ⟨hx, isGaugeField_congr hconf (hE.mono (bondsInside_subset hy)), ?_⟩
  cases s with
  | centred =>
    change ComplexMatrix2.familyDiameter (contourHolonomies W' y x) < centreOfMassDiameter
    rw [← contourHolonomies_congr R hE hy hx]
    exact hs
  | cornered => trivial
private theorem baseTransport_congr (R : BlockRoutes c μ)
    (hE : Set.EqOn W W' (bondsInDoubleBlock c))
    (s : AveragingScheme) : baseTransport s W c = baseTransport s W' c := by
  cases s with
  | centred =>
    change pathHolonomy W (axialPath (c.source.toSublattice (levelDepth K n))
        (c.target.toSublattice (levelDepth K n))) =
      pathHolonomy W' (axialPath (c.source.toSublattice (levelDepth K n))
        (c.target.toSublattice (levelDepth K n)))
    rw [R.axial.2.1]
    exact pathHolonomy_congr fun b hb => hE (R.paths.2 _ R.source_mem b hb)
  | cornered =>
    change pathHolonomy W (axialPath (blockAnchor (levelDepth K n) c.source)
        (blockAnchor (levelDepth K n) c.target)) =
      pathHolonomy W' (axialPath (blockAnchor (levelDepth K n) c.source)
        (blockAnchor (levelDepth K n) c.target))
    rw [R.axial.2.2]
    exact pathHolonomy_congr fun b hb => hE (R.paths.2 _ R.anchor_mem b hb)
private theorem shiftAcross_mem (R : BlockRoutes c μ) {x : SiteAtLevel L m K n}
    (hx : x ∈ sitesInBlock (levelDepth K n) c.source) :
    shiftAcross c x ∈ sitesInBlock (levelDepth K n) c.target := by
  rw [R.coords.2.2.2.2.1 x hx, ← R.coords.2.2.2.1]
  exact ⟨x, hx, rfl⟩
private theorem localDefect_congr (R : BlockRoutes c μ) (hE : Set.EqOn W W' (bondsInDoubleBlock c))
    (s : AveragingScheme) {x : SiteAtLevel L m K n}
    (hx : x ∈ sitesInBlock (levelDepth K n) c.source) :
    localDefect s W c x = localDefect s W' c x := by
  unfold localDefect
  rw [contourHolonomy_congr R hE s (Or.inl rfl) hx,
    contourHolonomy_congr R hE s (Or.inr rfl) (shiftAcross_mem R hx),
    baseTransport_congr R hE s,
    pathHolonomy_congr (W := W) (W' := W') fun b hb => hE (R.paths.2 x hx b hb)]
private theorem schemeBlockAverage_congr (R : BlockRoutes c μ) (hc : c.IsPositivelyOriented)
    (hE : Set.EqOn W W' (bondsInDoubleBlock c)) (s : AveragingScheme) :
    schemeBlockAverage s W c = schemeBlockAverage s W' c := by
  simp only [schemeBlockAverage, if_pos hc]
  unfold positiveBondAverage
  rw [finsum_mem_congr rfl fun x hx => by rw [localDefect_congr R hE s hx],
    baseTransport_congr R hE s]
private theorem areContourHolonomiesDefined_congr (R : BlockRoutes c μ)
    (hE : Set.EqOn W W' (bondsInDoubleBlock c))
    (s : AveragingScheme) (h : AreContourHolonomiesDefined s W c) :
    AreContourHolonomiesDefined s W' c :=
  ⟨fun x hx => isContourHolonomyDefined_congr R hE s (Or.inl rfl) (h.1 x hx),
    fun x hx => isContourHolonomyDefined_congr R hE s (Or.inr rfl) (h.2 x hx)⟩
private theorem isSchemeAverageDefined_congr (R : BlockRoutes c μ)
    (hE : Set.EqOn W W' (bondsInDoubleBlock c))
    (s : AveragingScheme) (h : IsSchemeAverageDefined s W c) : IsSchemeAverageDefined s W' c :=
  ⟨isGaugeField_congr h.1 hE, areContourHolonomiesDefined_congr R hE s h.2.1, fun x hx => by
    rw [← localDefect_congr R hE s hx]
    exact h.2.2 x hx⟩
private theorem twistedConfig_eqOn (a : LieBondField (doubleBlockSymmetricSet c))
    (hE : Set.EqOn W W' (bondsInDoubleBlock c)) :
    Set.EqOn (twistedConfig c a W) (twistedConfig c a W') (bondsInDoubleBlock c) := by
  intro b hb
  have hr : b.opposite ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := ⟨hb.2, hb.1⟩
  simp only [twistedConfig, expTwist]
  by_cases hp : b.IsPositivelyOriented
  · simp only [if_pos hp]
    rw [hE hb]
  · simp only [if_neg hp]
    rw [hE hr]
variable (a : LieBondField (doubleBlockSymmetricSet c))
private theorem stepRatio_congr (R : BlockRoutes c μ) (hE : Set.EqOn W W' (bondsInDoubleBlock c))
    (s : AveragingScheme)
    {y : SiteAtLevel L m K (n + 1)} (hy : y = c.source ∨ y = c.target) {x : SiteAtLevel L m K n}
    (hx : x ∈ sitesInBlock (levelDepth K n) y) : stepRatio s c a W y x = stepRatio s c a W' y x := by
  unfold stepRatio
  rw [contourHolonomy_congr R (twistedConfig_eqOn a hE) s hy hx, contourHolonomy_congr R hE s hy hx]
private theorem stepLog_congr (R : BlockRoutes c μ) (hE : Set.EqOn W W' (bondsInDoubleBlock c))
    (s : AveragingScheme)
    {y : SiteAtLevel L m K (n + 1)} (hy : y = c.source ∨ y = c.target) {x : SiteAtLevel L m K n}
    (hx : x ∈ sitesInBlock (levelDepth K n) y) :
    stepLog s c a W y x = stepLog s c a W' y x := by
  unfold stepLog
  rw [stepRatio_congr a R hE s hy hx]
private theorem stepGauge_congr (R : BlockRoutes c μ) (hE : Set.EqOn W W' (bondsInDoubleBlock c))
    (s : AveragingScheme) {y : SiteAtLevel L m K (n + 1)} (hy : y = c.source ∨ y = c.target) :
    stepGauge s c a W y = stepGauge s c a W' y := by
  unfold stepGauge
  rw [finsum_mem_congr rfl fun x hx => stepLog_congr a R hE s hy hx]
private theorem stepGaugeLogarithm_congr (R : BlockRoutes c μ)
    (hE : Set.EqOn W W' (bondsInDoubleBlock c))
    (s : AveragingScheme) {y : SiteAtLevel L m K (n + 1)} (hy : y = c.source ∨ y = c.target) :
    stepGaugeLogarithm s c a W y = stepGaugeLogarithm s c a W' y := by
  unfold stepGaugeLogarithm
  rw [stepGauge_congr a R hE s hy]
private theorem stepProduct_congr (R : BlockRoutes c μ) (hc : c.IsPositivelyOriented)
    (hE : Set.EqOn W W' (bondsInDoubleBlock c)) (s : AveragingScheme) :
    stepProduct s c a W = stepProduct s c a W' := by
  unfold stepProduct
  rw [stepGauge_congr a R hE s (Or.inl rfl), stepGauge_congr a R hE s (Or.inr rfl),
    schemeBlockAverage_congr R hc (twistedConfig_eqOn a hE) s, schemeBlockAverage_congr R hc hE s]
private theorem stepVariable_congr (R : BlockRoutes c μ) (hc : c.IsPositivelyOriented)
    (hE : Set.EqOn W W' (bondsInDoubleBlock c)) (s : AveragingScheme) :
    stepVariable s c a W = stepVariable s c a W' := by
  unfold stepVariable
  rw [stepProduct_congr a R hc hE s]
private theorem isContourRatioLogDefined_congr (R : BlockRoutes c μ)
    (hE : Set.EqOn W W' (bondsInDoubleBlock c))
    (s : AveragingScheme) {y : SiteAtLevel L m K (n + 1)} (hy : y = c.source ∨ y = c.target)
    {x : SiteAtLevel L m K n} (hx : x ∈ sitesInBlock (levelDepth K n) y)
    (h : IsContourRatioLogDefined s c a W y x) : IsContourRatioLogDefined s c a W' y x := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨isContourHolonomyDefined_congr R (twistedConfig_eqOn a hE) s hy h₁,
    isContourHolonomyDefined_congr R hE s hy h₂, ?_⟩
  rw [← stepRatio_congr a R hE s hy hx]
  exact h₃
private theorem stepVariableDefined_congr (R : BlockRoutes c μ) (hc : c.IsPositivelyOriented)
    (hE : Set.EqOn W W' (bondsInDoubleBlock c)) (s : AveragingScheme)
    (h : StepVariableDefined s c a W) : StepVariableDefined s c a W' := by
  obtain ⟨⟨h₁, h₂, h₃, h₄⟩, h₅, h₆, h₇⟩ := h
  refine ⟨⟨areContourHolonomiesDefined_congr R (twistedConfig_eqOn a hE) s h₁,
    areContourHolonomiesDefined_congr R hE s h₂,
    fun x hx => ?_, fun x hx => ?_⟩, isSchemeAverageDefined_congr R (twistedConfig_eqOn a hE) s h₅,
    isSchemeAverageDefined_congr R hE s h₆, ?_⟩
  · rw [← stepRatio_congr a R hE s (Or.inl rfl) hx]
    exact h₃ x hx
  · rw [← stepRatio_congr a R hE s (Or.inr rfl) hx]
    exact h₄ x hx
  · rw [← stepProduct_congr a R hc hE s]
    exact h₇
private theorem stepQuantitiesBounded_congr (R : BlockRoutes c μ) (hc : c.IsPositivelyOriented)
    (hE : Set.EqOn W W' (bondsInDoubleBlock c)) (s : AveragingScheme)
    (h : StepQuantitiesBounded s c a W) : StepQuantitiesBounded s c a W' where
  log_bound := fun y hy x hx => by
    have hy' := eq_source_or_target hy
    refine ⟨isContourRatioLogDefined_congr a R hE s hy' hx (h.log_bound y hy x hx).1, ?_⟩
    rw [← stepLog_congr a R hE s hy' hx]
    exact (h.log_bound y hy x hx).2
  gauge_bound := fun y hy => by
    have hy' := eq_source_or_target hy
    obtain ⟨h₁, h₂, h₃⟩ := h.gauge_bound y hy
    refine ⟨fun x hx => isContourRatioLogDefined_congr a R hE s hy' hx (h₁ x hx), ?_, ?_⟩
    · rw [← stepGauge_congr a R hE s hy']
      exact h₂
    · rw [← stepGaugeLogarithm_congr a R hE s hy']
      exact h₃
  variable_bound := by
    refine ⟨stepVariableDefined_congr a R hc hE s h.variable_bound.1, ?_⟩
    rw [← stepVariable_congr a R hc hE s]
    exact h.variable_bound.2
end Locality
section Back
variable {L m K n : ℕ} {c : BondAtLevel L m K (n + 1)} {μ : Fin 4}
private def conjugatedField (u : SiteAtLevel L m K n → ComplexMatrix2)
    (a : LieBondField (doubleBlockSymmetricSet c)) : LieBondField (doubleBlockSymmetricSet c) :=
  fun b => ⟨ComplexMatrix2.conjugateBy (u b.1.source) (a b : ComplexMatrix2),
    conjugateBy_mem_traceless _ (a b).2⟩
private theorem supOperatorNorm_conjugatedField (hN : ComplexMatrix2.OperatorNormUnderConjugation)
    {u : SiteAtLevel L m K n → ComplexMatrix2} (hu : ∀ x, u x ∈ compactGaugeGroup)
    (a : LieBondField (doubleBlockSymmetricSet c)) :
    supOperatorNorm (conjugatedField u a) = supOperatorNorm a :=
  iSup_congr fun _ => hN.2.1 _ _ (mem_unitaryGroup_of_mem (hu _))
private theorem logSeries_conj (hN : ComplexMatrix2.OperatorNormUnderConjugation)
    {g X : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) (h : ComplexMatrix2.operatorNorm (X - 1) < 1) :
    ComplexMatrix2.operatorNorm (g * X * g⁻¹ - 1) < 1 ∧
      Complex.I⁻¹ • ComplexMatrix2.logSeries (g * X * g⁻¹) =
        ComplexMatrix2.conjugateBy g (Complex.I⁻¹ • ComplexMatrix2.logSeries X) := by
  have hclose := hN.2.2.2.2.2.2 g X (mem_unitaryGroup_of_mem hg) h
  have hunit : IsUnit g :=
    (Matrix.isUnit_iff_isUnit_det _).2 (by rw [det_eq_one hg]; exact isUnit_one)
  refine ⟨hclose, ?_⟩
  rw [hN.2.2.2.2.2.1 g X hunit h hclose]
  simp only [ComplexMatrix2.conjugateBy, mul_smul_comm, smul_mul_assoc]
private theorem stepObjects_eq_conj (hC : StepObjectsGaugeCovariance)
    (hN : ComplexMatrix2.OperatorNormUnderConjugation) (hL : IsAdmissibleBlockingFactor L)
    (hm : 0 < m) (hn : n < K) (hc : c.IsPositivelyOriented) (R : BlockRoutes c μ)
    (s : AveragingScheme) {r : ℝ}
    (hr : IsAdmissiblePolydiscRadius L r) {W₀ : BondAtLevel L m K n → ComplexMatrix2}
    {u : SiteAtLevel L m K n → ComplexMatrix2}
    (hu : ∀ x, u x ∈ compactGaugeGroup)
    (hW₁ : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) (gaugeTransform u W₀))
    {a₀ : LieBondField (doubleBlockSymmetricSet c)} (ha₀ : supOperatorNorm a₀ < r)
    (hE : Set.EqOn (expOfBondField c a₀) (gaugeTransform u W₀) (bondsInDoubleBlock c))
    {a : LieBondField (doubleBlockSymmetricSet c)} (ha : supOperatorNorm a < r) :
    StepQuantitiesBounded s c a W₀ ∧
      (∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
        ∀ x ∈ sitesInBlock (levelDepth K n) y, stepLog s c a W₀ y x =
          ComplexMatrix2.conjugateBy (u (schemeBaseSite s (levelDepth K n) y))⁻¹
            (stepLog s c (conjugatedField u a) (expOfBondField c a₀) y x)) ∧
      (∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
        stepGaugeLogarithm s c a W₀ y =
          ComplexMatrix2.conjugateBy (u (schemeBaseSite s (levelDepth K n) y))⁻¹
            (stepGaugeLogarithm s c (conjugatedField u a) (expOfBondField c a₀) y)) ∧
      stepVariable s c a W₀ =
        ComplexMatrix2.conjugateBy (u (schemeBaseSite s (levelDepth K n) c.source))⁻¹
          (stepVariable s c (conjugatedField u a) (expOfBondField c a₀)) := by
  have hsup : supOperatorNorm (conjugatedField u a) < r := by
    rw [supOperatorNorm_conjugatedField hN hu]
    exact ha
  have B := (hr.bounds_on m K n hm hn s c hc a₀ (conjugatedField u a) ha₀ hsup).quantities
  have B₁ := stepQuantitiesBounded_congr (conjugatedField u a) R hc hE s B
  have hv : ∀ x, (fun x => (u x)⁻¹) x ∈ compactGaugeGroup :=
    fun x => inv_mem_specialUnitary (hu x)
  have hback : gaugeTransform (fun x => (u x)⁻¹) (gaugeTransform u W₀) = W₀ := by
    funext b
    change (u b.source)⁻¹ * (u b.source * W₀ b * (u b.target)⁻¹) * ((u b.target)⁻¹)⁻¹ = W₀ b
    rw [inv_inv_of (hu _)]
    calc (u b.source)⁻¹ * (u b.source * W₀ b * (u b.target)⁻¹) * u b.target
        = ((u b.source)⁻¹ * u b.source) * W₀ b * ((u b.target)⁻¹ * u b.target) := by
          simp only [mul_assoc]
      _ = W₀ b := by rw [inv_mul_self_of (hu _), inv_mul_self_of (hu _), one_mul, mul_one]
  have hrel : ∀ b : PositiveBondsOf (doubleBlockSymmetricSet c), (a b : ComplexMatrix2) =
      ComplexMatrix2.conjugateBy ((fun x => (u x)⁻¹) b.1.source)
        (conjugatedField u a b : ComplexMatrix2) := by
    intro b
    change (a b : ComplexMatrix2) =
      (u b.1.source)⁻¹ * (u b.1.source * (a b : ComplexMatrix2) * (u b.1.source)⁻¹) *
        ((u b.1.source)⁻¹)⁻¹
    rw [inv_inv_of (hu _)]
    calc (a b : ComplexMatrix2)
        = ((u b.1.source)⁻¹ * u b.1.source) * (a b : ComplexMatrix2) *
            ((u b.1.source)⁻¹ * u b.1.source) := by
          rw [inv_mul_self_of (hu _), one_mul, mul_one]
      _ = _ := by simp only [mul_assoc]
  have H := hC L hL m K n hm hn s c hc (gaugeTransform u W₀) (conjugatedField u a) a
    (fun x => (u x)⁻¹) hv hrel hW₁
  have Hl := H.log_eq
  have Hg := H.gauge_eq
  have Hv := H.variable_eq
  rw [hback] at Hl Hg Hv
  have hAd : ∀ (g X : ComplexMatrix2), g ∈ ComplexMatrix2.specialUnitary →
      ComplexMatrix2.operatorNorm (ComplexMatrix2.conjugateBy g X) =
        ComplexMatrix2.operatorNorm X :=
    fun g X hg => hN.2.1 X g (mem_unitaryGroup_of_mem hg)
  refine ⟨⟨fun y hy x hx => ?_, fun y hy => ?_, ?_⟩, fun y hy x hx => ?_, fun y hy => ?_, ?_⟩
  · obtain ⟨f, hle⟩ := B₁.log_bound y hy x hx
    obtain ⟨f', e⟩ := Hl y hy x hx f
    refine ⟨f', ?_⟩
    rw [e, hAd _ _ (hv _)]
    exact hle
  · obtain ⟨f, h₁, h₂⟩ := B₁.gauge_bound y hy
    obtain ⟨f', e⟩ := Hg y hy f
    obtain ⟨k₁, k₂⟩ := logSeries_conj hN (hv (schemeBaseSite s (levelDepth K n) y)) h₁
    refine ⟨f', ?_, ?_⟩
    · rw [e]
      exact k₁
    · unfold stepGaugeLogarithm
      rw [e, k₂, hAd _ _ (hv _)]
      exact h₂
  · obtain ⟨f, hle⟩ := B₁.variable_bound
    obtain ⟨f', e⟩ := Hv f
    refine ⟨f', ?_⟩
    rw [e, hAd _ _ (hv _)]
    exact hle
  · obtain ⟨f, -⟩ := B₁.log_bound y hy x hx
    rw [(Hl y hy x hx f).2, ← stepLog_congr (conjugatedField u a) R hE s (eq_source_or_target hy) hx]
  · obtain ⟨f, h₁, -⟩ := B₁.gauge_bound y hy
    obtain ⟨-, e⟩ := Hg y hy f
    obtain ⟨-, k₂⟩ := logSeries_conj hN (hv (schemeBaseSite s (levelDepth K n) y)) h₁
    rw [stepGaugeLogarithm_congr (conjugatedField u a) R hE s (eq_source_or_target hy)]
    unfold stepGaugeLogarithm
    rw [e, k₂]
  · obtain ⟨f, -⟩ := B₁.variable_bound
    rw [(Hv f).2, ← stepVariable_congr (conjugatedField u a) R hc hE s]
end Back
section Comb
variable {L m K n : ℕ} {j : ℤ}
private theorem sum_smul_unitStep_apply (d : Fin 4 → ℤ) (ν : Fin 4) :
    ((∑ μ, d μ • unitStep L m j μ : Site L m j) : FourTorus L m) ν =
      (((d ν : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) := by apply _root_.YangMills.Construction.PeriodicLattice.CombGaugeOnBox.coe_sum_zsmul_unitStep <;> assumption
private theorem coordCount_doubleBlock_le {c : BondAtLevel L m K (n + 1)} {μ : Fin 4}
    (hL : IsAdmissibleBlockingFactor L) (R : BlockRoutes c μ) (ν : Fin 4) :
    coordCount ν (sitesIn (bondDoubleBlock c) : Set (SiteAtLevel L m K n)) ≤
      ((2 * L - 1 : ℕ) : ℕ∞) + 1 := by
  have hco := R.coords.2.2.2.2.2
  have hodd : 2 * centreToFaceSteps L + 1 = (L : ℤ) := by
    obtain ⟨t, ht⟩ := hL.1
    unfold centreToFaceSteps
    omega
  let f : ℤ → AddCircle (torusSide L m) := fun t =>
    ((c.source.toSublattice (levelDepth K n) : SiteAtLevel L m K n) : FourTorus L m) ν +
      (((t : ℝ) * meshSize L (levelDepth K n) : ℝ) : AddCircle (torusSide L m))
  let S : Finset ℤ := Finset.Icc (-centreToFaceSteps L) (centreToFaceSteps L + L)
  have hsub : (fun x : SiteAtLevel L m K n => (x : FourTorus L m) ν) ''
      (sitesIn (bondDoubleBlock c) : Set (SiteAtLevel L m K n)) ⊆ f '' (S : Set ℤ) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : FourTorus L m) ∈ bondDoubleBlock c := hx
    rw [← hco.2] at hx'
    obtain ⟨p, hp, hxp⟩ := hx'
    refine ⟨p ν, ?_, ?_⟩
    · have hb : -centreToFaceSteps L ≤ p ν ∧ p ν ≤ centreToFaceSteps L + L := by
        by_cases hν : ν = μ
        · subst hν
          exact ⟨hp.1, hp.2.1⟩
        · have h₁ := abs_le.1 (hp.2.2 ν hν)
          exact ⟨h₁.1, by have := h₁.2; omega⟩
      exact Finset.mem_coe.2 (Finset.mem_Icc.2 hb)
    · change ((c.source.toSublattice (levelDepth K n) : SiteAtLevel L m K n) : FourTorus L m) ν + _ =
        (x : FourTorus L m) ν
      beta_reduce at hxp
      rw [← hxp, offsetSite, ← sum_smul_unitStep_apply p ν]
      simp
  have hcard : (S.card : ℕ∞) = ((2 * L - 1 : ℕ) : ℕ∞) + 1 := by
    have h₁ : S.card = 2 * L := by
      simp only [S, Int.card_Icc]
      omega
    have h₂ : 2 * L = (2 * L - 1) + 1 := by have := hL.2; omega
    rw [h₁, h₂]
    simp
  calc coordCount ν (sitesIn (bondDoubleBlock c) : Set (SiteAtLevel L m K n))
      ≤ (f '' (S : Set ℤ)).encard := Set.encard_le_encard hsub
    _ ≤ (S : Set ℤ).encard := Set.encard_image_le _ _
    _ = S.card := Set.encard_coe_eq_coe_finsetCard S
    _ = _ := hcard
private theorem pathHolonomy_mem {W : BondAtLevel L m K n → ComplexMatrix2}
    (h : ∀ b, W b ∈ ComplexMatrix2.specialUnitary)
    (Γ : List (BondAtLevel L m K n)) : pathHolonomy W Γ ∈ ComplexMatrix2.specialUnitary := by
  induction Γ with
  | nil => exact one_mem _
  | cons b Γ ih =>
    simp only [pathHolonomy, List.map_cons, List.prod_cons]
    exact mul_mem (h b) ih
abbrev _root_.YangMills.DeltaSharedProofs.p502631 := @pathHolonomy_mem
private theorem exists_comb_gauge_near_exp (hComb : CombTransportOnBox.Statement)
    (hBox : DoubleBlockFromLowestCorner) (hL : IsAdmissibleBlockingFactor L)
    (hm : 0 < m) (hn : n < K) {c : BondAtLevel L m K (n + 1)} {μ : Fin 4}
    (hμ : c.target - c.source = unitStep L m (levelDepth K (n + 1)) μ) (R : BlockRoutes c μ) {r : ℝ}
    (hr : IsAdmissiblePolydiscRadius L r) {W₀ : BondAtLevel L m K n → ComplexMatrix2}
    (hW : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) W₀)
    (hϖ : doubleBlockCurvature W₀ c ≤ curvatureBound L r) :
    ∃ (u : SiteAtLevel L m K n → ComplexMatrix2) (a₀ : LieBondField (doubleBlockSymmetricSet c)),
      (∀ x, u x ∈ compactGaugeGroup) ∧
      IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) (gaugeTransform u W₀) ∧
      supOperatorNorm a₀ < r ∧
      Set.EqOn (expOfBondField c a₀) (gaugeTransform u W₀) (bondsInDoubleBlock c) := by
  classical
  let Y : Set (SiteAtLevel L m K n) := sitesIn (bondDoubleBlock c)
  let W' : BondAtLevel L m K n → ComplexMatrix2 :=
    fun b => if b ∈ bondsInDoubleBlock c then W₀ b else 1
  have hW'eq : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), W' b = W₀ b :=
    fun b hb => if_pos hb
  have hW'G : ∀ b, W' b ∈ ComplexMatrix2.specialUnitary := by
    intro b
    by_cases h : b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n))
    · rw [hW'eq b h]
      exact hW.1 b h
    · have : W' b = 1 := if_neg h
      rw [this]
      exact one_mem _
  have hconf : IsGaugeFieldWithin Y W' := by
    refine ⟨fun b _ => hW'G b, fun b hb => ?_⟩
    have hb' : b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := hb
    have hr' : b.opposite ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := ⟨hb'.2, hb'.1⟩
    rw [hW'eq _ hr', hW'eq _ hb']
    exact hW.2 b hb'
  have hbox : IsSiteBox (levelDepth K n) Y := (hBox L m K hL hm n hn c μ hμ).2.1
  have hoY : c.source.toSublattice (levelDepth K n) ∈ Y := Or.inl R.source_mem
  have hplaq_eq : ∀ p : PlaquetteAtLevel L m K n, p.LiesIn Y →
      plaquetteHolonomy W' p = plaquetteHolonomy W₀ p := by
    intro p hp
    exact pathHolonomy_congr fun b hb => hW'eq b (Plaquette.LiesIn.boundaryBonds_liesIn hp b hb)
  have hbdd : BddAbove (Set.range fun q : ↥(doubleBlockPlaquettes c :
      Set (PlaquetteAtLevel L m K n)) =>
        ComplexMatrix2.operatorNorm (plaquetteHolonomy W₀ q.1 - 1)) := by
    refine ⟨2, ?_⟩
    rintro _ ⟨q, rfl⟩
    have hq : q.1.LiesIn Y := fun x hx => q.2 x hx
    change ComplexMatrix2.operatorNorm (plaquetteHolonomy W₀ q.1 - 1) ≤ 2
    rw [← hplaq_eq _ hq]
    exact operatorNorm_sub_one_le_two (pathHolonomy_mem hW'G _)
  have hplaq : ∀ p : PlaquetteAtLevel L m K n, p.LiesIn Y →
      ComplexMatrix2.operatorNorm (plaquetteHolonomy W' p - 1) ≤ doubleBlockCurvature W₀ c := by
    intro p hp
    rw [hplaq_eq p hp]
    have hmem : p ∈ (doubleBlockPlaquettes c : Set (PlaquetteAtLevel L m K n)) :=
      fun x hx => hp hx
    exact le_ciSup hbdd
      (⟨p, hmem⟩ : ↥(doubleBlockPlaquettes c : Set (PlaquetteAtLevel L m K n)))
  have hϖ0 : 0 ≤ doubleBlockCurvature W₀ c := Real.iSup_nonneg fun _ => norm_nonneg _
  have hcomb := hComb L hL m K n hm hn.le Y (2 * L - 1) (c.source.toSublattice (levelDepth K n)) W'
    (doubleBlockCurvature W₀ c) hbox (coordCount_doubleBlock_le hL R) hoY hconf hϖ0 hplaq
  obtain ⟨-, -, h₃, -⟩ := hcomb
  set ϖ := doubleBlockCurvature W₀ c with hϖdef
  have hL0 : (0 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 0 < L)
  have hcast : ((2 * L - 1 : ℕ) : ℝ) = 2 * L - 1 := by
    have h₁ : 1 ≤ 2 * L := by have := hL.2; omega
    rw [Nat.cast_sub h₁]
    push_cast
    ring
  have hpi := Real.pi_gt_three
  have hb : ϖ ≤ r / (6 * Real.pi * (L : ℝ)) :=
    hϖ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hq : 6 * (Real.pi * (L * ϖ)) ≤ r := by
    have h₀ : 0 < 6 * Real.pi * (L : ℝ) := by positivity
    have := (le_div_iff₀ h₀).1 hb
    linarith
  have hLq : 0 ≤ (L : ℝ) * ϖ := mul_nonneg hL0.le hϖ0
  have hπq : 3 * ((L : ℝ) * ϖ) ≤ Real.pi * (L * ϖ) := mul_le_mul_of_nonneg_right hpi.le hLq
  have hπϖ : 0 ≤ Real.pi * ϖ := mul_nonneg Real.pi_pos.le hϖ0
  have hsmall : 3 * ((2 * L - 1 : ℕ) : ℝ) * ϖ < 2 := by
    rw [hcast]
    have h₁ : 3 * (2 * (L : ℝ) - 1) * ϖ = 6 * (L * ϖ) - 3 * ϖ := by ring
    have h₂ := hr.radius_le
    rw [h₁]
    linarith
  obtain ⟨a, -, hgauge, hsup⟩ := h₃ hsmall
  have hu : ∀ x, combTransport W' (c.source.toSublattice (levelDepth K n)) x ∈ compactGaugeGroup :=
    fun x => pathHolonomy_mem hW'G _
  have hW₁ : IsGaugeField complexGaugeGroup (bondsInDoubleBlock c)
      (gaugeTransform (combTransport W' (c.source.toSublattice (levelDepth K n))) W₀) := by
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · change (_ * _ * _ : ComplexMatrix2).det = 1
      rw [Matrix.det_mul, Matrix.det_mul, det_eq_one (hu _), det_eq_one (hW.1 b hb),
        det_eq_one (inv_mem_specialUnitary (hu _))]
      simp
    · change _ * W₀ b.opposite * _ = (_ * W₀ b * _)⁻¹
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_inv_of (hu _), hW.2 b hb, mul_assoc]
      rfl
  have hgauge' : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)),
      gaugeTransform (combTransport W' (c.source.toSublattice (levelDepth K n))) W₀ b =
        ComplexMatrix2.matExp (Complex.I •
          (LieBondField.eval (P := doubleBlockSymmetricSet c) a b : ComplexMatrix2)) := by
    intro b hb
    have h := hgauge b hb
    simp only [gaugeTransform] at h ⊢
    rw [hW'eq b hb] at h
    exact h
  refine ⟨combTransport W' (c.source.toSublattice (levelDepth K n)), a, hu, hW₁, ?_, fun b hb => ?_⟩
  · have h₁ : 3 * Real.pi / 2 * ((2 * L - 1 : ℕ) : ℝ) * ϖ =
        3 * (Real.pi * (L * ϖ)) - 3 / 2 * (Real.pi * ϖ) := by
      rw [hcast]
      ring
    have h₂ := hr.radius_pos
    have h₃ : supOperatorNorm a ≤ _ := hsup
    change supOperatorNorm a < r
    rw [h₁] at h₃
    linarith
  · have hr' : b.opposite ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := ⟨hb.2, hb.1⟩
    simp only [expOfBondField, twistedConfig, expTwist, trivialGaugeField, mul_one]
    by_cases hp : b.IsPositivelyOriented
    · simp only [if_pos hp]
      exact (hgauge' b hb).symm
    · simp only [if_neg hp]
      rw [← hgauge' _ hr']
      exact (hW₁.2 b.opposite hr').symm
end Comb
section Affine
open Matrices.GroupLieProduct
variable {L m K n : ℕ} {c : BondAtLevel L m K (n + 1)}
private def conjugateByLinear (V : ComplexMatrix2) : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 where
  toFun := ComplexMatrix2.conjugateBy V
  map_add' X Y := by simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
  map_smul' t X := by simp [ComplexMatrix2.conjugateBy]
private def pairLinear (u : SiteAtLevel L m K n → ComplexMatrix2) :
    (PositiveBondsOf (doubleBlockSymmetricSet c) → ComplexMatrix2) →ₗ[ℂ]
      (PositiveBondsOf (doubleBlockSymmetricSet c) ⊕ PositiveBondsOf (doubleBlockSymmetricSet c) →
        ComplexMatrix2) where
  toFun A := Sum.elim 0 fun b => ComplexMatrix2.conjugateBy (u b.1.source) (A b)
  map_add' A B := by
    funext i
    rcases i with b | b <;> simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
  map_smul' t A := by
    funext i
    rcases i with b | b <;> simp [ComplexMatrix2.conjugateBy]
private theorem coe_tracelessPart {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    (tracelessPart X : ComplexMatrix2) = X := by apply _root_.YangMills.Construction.PeriodicLattice.BoundedStepHolomorphy.tracelessPart_coe <;> assumption
private theorem firstComponent_affine (u : SiteAtLevel L m K n → ComplexMatrix2)
    (a₀ : LieBondField (doubleBlockSymmetricSet c))
    (A : PositiveBondsOf (doubleBlockSymmetricSet c) → ComplexMatrix2) :
    firstComponent (Sum.elim (fun b => (a₀ b : ComplexMatrix2)) 0 + pairLinear u A) = a₀ := by
  funext b
  apply Subtype.ext
  change (tracelessPart ((a₀ b : ComplexMatrix2) + 0) : ComplexMatrix2) = a₀ b
  rw [add_zero, coe_tracelessPart (a₀ b).2]
private theorem secondComponent_affine (u : SiteAtLevel L m K n → ComplexMatrix2)
    (a₀ : LieBondField (doubleBlockSymmetricSet c))
    {A : PositiveBondsOf (doubleBlockSymmetricSet c) → ComplexMatrix2}
    (hA : A ∈ tracelessPi (PositiveBondsOf (doubleBlockSymmetricSet c))) :
    secondComponent (Sum.elim (fun b => (a₀ b : ComplexMatrix2)) 0 + pairLinear u A) =
      conjugatedField u fun b => tracelessPart (A b) := by
  funext b
  apply Subtype.ext
  change (tracelessPart (0 + ComplexMatrix2.conjugateBy (u b.1.source) (A b)) : ComplexMatrix2) =
    ComplexMatrix2.conjugateBy (u b.1.source) (tracelessPart (A b) : ComplexMatrix2)
  rw [zero_add, coe_tracelessPart (conjugateBy_mem_traceless _ (hA b)), coe_tracelessPart (hA b)]
end Affine
end StepObjectsNearSmallCurvatureProof
open StepObjectsNearSmallCurvatureProof Matrices.GroupLieProduct in
theorem stepObjectsNearSmallCurvature_holds
    (hC : StepObjectsGaugeCovariance) (hComb : CombTransportOnBox.Statement)
    (hPaths : BlockPaths.Statement)
    (hBox : DoubleBlockFromLowestCorner)
    (hN : ComplexMatrix2.OperatorNormUnderConjugation)
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ExpChartHolomorphy.ExpChartTheory) :
    StepObjectsNearSmallCurvature := by
  intro L hL r hr m K n hm hn s c hc W₀ hW hϖ
  obtain ⟨μ, hμ⟩ := id hc
  have R := blockRoutes hPaths hL hm hn c hμ
  obtain ⟨u, a₀, hu, hW₁, ha₀, hEq⟩ :=
    exists_comb_gauge_near_exp hComb hBox hL hm hn hμ R hr hW hϖ
  have hobj := fun (a : LieBondField (doubleBlockSymmetricSet c)) (ha : supOperatorNorm a < r) =>
    stepObjects_eq_conj hC hN hL hm hn hc R s hr hu hW₁ ha₀ hEq ha
  refine ⟨fun a ha => (hobj a ha).1, fun ρ hρ ft β => ?_⟩
  obtain ⟨H₁, H₂, H₃, -⟩ := hr.holomorphic_on m K n hm hn s c hc inferInstance β
  have hp₀ : Sum.elim (fun b => (a₀ b : ComplexMatrix2)) 0 ∈
      tracelessPi (PositiveBondsOf (doubleBlockSymmetricSet c) ⊕
        PositiveBondsOf (doubleBlockSymmetricSet c)) := by
    rintro (b | b)
    · exact (a₀ b).2
    · exact Submodule.zero_mem _
  have hΘ : ∀ A ∈ tracelessPi (PositiveBondsOf (doubleBlockSymmetricSet c)),
      pairLinear u A ∈ tracelessPi
        (PositiveBondsOf (doubleBlockSymmetricSet c) ⊕ PositiveBondsOf (doubleBlockSymmetricSet c)) := by
    rintro A hA (b | b)
    · exact Submodule.zero_mem _
    · exact conjugateBy_mem_traceless _ (hA b)
  have hball : ∀ A ∈ supBall (PositiveBondsOf (doubleBlockSymmetricSet c)) ρ,
      Sum.elim (fun b => (a₀ b : ComplexMatrix2)) 0 + pairLinear u A ∈ supBall
        (PositiveBondsOf (doubleBlockSymmetricSet c) ⊕ PositiveBondsOf (doubleBlockSymmetricSet c))
          r := by
    intro A hA
    refine ⟨fun i => Submodule.add_mem _ (hp₀ i) (hΘ A hA.1 i), ?_⟩
    have hAr : supNorm A < r := lt_of_lt_of_le hA.2 hρ
    have ha₀' : supNorm (fun b => (a₀ b : ComplexMatrix2)) < r := ha₀
    refine lt_of_le_of_lt (supNorm_le (t := max (supNorm fun b => (a₀ b : ComplexMatrix2)) (supNorm A))
      (le_max_of_le_left (supNorm_nonneg _)) ?_) (max_lt ha₀' hAr)
    rintro (b | b)
    · change ComplexMatrix2.operatorNorm ((a₀ b : ComplexMatrix2) + 0) ≤ _
      rw [add_zero]
      exact le_max_of_le_left (operatorNorm_le_supNorm (fun b => (a₀ b : ComplexMatrix2)) b)
    · change ComplexMatrix2.operatorNorm (0 + ComplexMatrix2.conjugateBy (u b.1.source) (A b)) ≤ _
      rw [zero_add, show ComplexMatrix2.operatorNorm (ComplexMatrix2.conjugateBy (u b.1.source) (A b)) =
          ComplexMatrix2.operatorNorm (A b) from
        hN.2.1 _ _ (mem_unitaryGroup_of_mem (hu _))]
      exact le_max_of_le_right (operatorNorm_le_supNorm A b)
  have hsup : ∀ A ∈ supBall (PositiveBondsOf (doubleBlockSymmetricSet c)) ρ,
      supOperatorNorm (fun b => tracelessPart (A b)) < r := by
    intro A hA
    have h : supOperatorNorm (fun b => tracelessPart (A b)) = supNorm A :=
      iSup_congr fun b => by rw [coe_tracelessPart (hA.1 b)]
    rw [h]
    exact lt_of_lt_of_le hA.2 hρ
  refine ⟨fun y hy x hx => ?_, fun y hy => ?_, ?_⟩
  · refine isHolomorphicOnTraceless_comp_affine hH hE β (pairLinear u) hp₀ hΘ hball
      (conjugateByLinear (u (schemeBaseSite s (levelDepth K n) y))⁻¹) (H₁ y hy x hx)
      fun A hA => ?_
    rw [firstComponent_affine, secondComponent_affine u a₀ hA.1]
    exact (hobj _ (hsup A hA)).2.1 y hy x hx
  · refine isHolomorphicOnTraceless_comp_affine hH hE β (pairLinear u) hp₀ hΘ hball
      (conjugateByLinear (u (schemeBaseSite s (levelDepth K n) y))⁻¹) (H₂ y hy) fun A hA => ?_
    rw [firstComponent_affine, secondComponent_affine u a₀ hA.1]
    exact (hobj _ (hsup A hA)).2.2.1 y hy
  · refine isHolomorphicOnTraceless_comp_affine hH hE β (pairLinear u) hp₀ hΘ hball
      (conjugateByLinear (u (schemeBaseSite s (levelDepth K n) c.source))⁻¹) H₃ fun A hA => ?_
    rw [firstComponent_affine, secondComponent_affine u a₀ hA.1]
    exact (hobj _ (hsup A hA)).2.2.2
end PeriodicLattice
end YangMills.Construction
