import Reconstruction.ComplexAnalysis.ProductAndHalfPlaneIdentity
import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import Reconstruction.MinkowskiSpace.ConeTubeAndLorentzGroup
import Reconstruction.MinkowskiSpace.LorentzInvarianceOfTheVacuumFunctions
import Reconstruction.MinkowskiSpace.ProductsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
open Matrix Filter Set
open scoped Topology ContDiff
noncomputable section
namespace YangMills.Construction.VacuumLorentzInvariance
open YangMills.Construction.MinkowskiSpace YangMills.Construction.WightmanTheory YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert YangMills.Construction.HilbertToolkit YangMills.Construction.ProjectionMeasures YangMills.Construction.PVMCalculus
theorem complexDifferentiableAt_fderiv_apply {b : ℕ} {W : (Fin b → ComplexVec4) → ℂ}
    {U : Set (Fin b → ComplexVec4)} (hU : IsOpen U)
    (hd : ∀ ζ ∈ U, DifferentiableAt ℂ W ζ) (hs : ContDiffOn ℝ 2 W U)
    (v : Fin b → ComplexVec4) {ζ : Fin b → ComplexVec4} (hζ : ζ ∈ U) :
    DifferentiableAt ℂ (fun ξ => fderiv ℂ W ξ v) ζ := by
  have hc : ContDiffAt ℝ 2 W ζ := hs.contDiffAt (hU.mem_nhds hζ)
  have hsymm : IsSymmSndFDerivAt ℝ W ζ := hc.isSymmSndFDerivAt (by simp)
  have hD : ∀ᶠ ξ in 𝓝 ζ, ∀ u, fderiv ℝ W ξ u = fderiv ℂ W ξ u := by
    filter_upwards [hU.mem_nhds hζ] with ξ hξ u
    rw [((hd ξ hξ).hasFDerivAt.restrictScalars ℝ).fderiv]
    rfl
  have hdiff : DifferentiableAt ℝ (fderiv ℝ W) ζ :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  set T2 := fderiv ℝ (fderiv ℝ W) ζ with hT2
  have happ : ∀ w, HasFDerivAt (fun ξ => fderiv ℝ W ξ w)
      ((ContinuousLinearMap.apply ℝ ℂ w).comp T2) ζ := fun w =>
    (ContinuousLinearMap.apply ℝ ℂ w).hasFDerivAt.comp ζ hdiff.hasFDerivAt
  have hlin : ∀ (c : ℂ) (u w), T2 u (c • w) = c • T2 u w := by
    intro c u w
    have h2 : HasFDerivAt (fun ξ => fderiv ℝ W ξ (c • w))
        (c • ((ContinuousLinearMap.apply ℝ ℂ w).comp T2)) ζ := by
      refine ((happ w).const_smul c).congr_of_eventuallyEq ?_
      filter_upwards [hD] with ξ hξ
      simp [hξ, map_smul]
    exact DFunLike.congr_fun ((happ (c • w)).unique h2) u
  let L : (Fin b → ComplexVec4) →ₗ[ℂ] ℂ :=
    { toFun := fun u => T2 u v
      map_add' := by intro a c; simp
      map_smul' := by
        intro c u
        simp only [RingHom.id_apply]
        rw [hsymm.eq (c • u) v, hlin, hsymm.eq v u] }
  have h3 : HasFDerivAt (fun ξ => fderiv ℝ W ξ v)
      ((LinearMap.toContinuousLinearMap L).restrictScalars ℝ) ζ := by
    have e : (LinearMap.toContinuousLinearMap L).restrictScalars ℝ =
        (ContinuousLinearMap.apply ℝ ℂ v).comp T2 := ContinuousLinearMap.ext fun u => rfl
    rw [e]
    exact happ v
  have h4 : HasFDerivAt (fun ξ => fderiv ℝ W ξ v) (LinearMap.toContinuousLinearMap L) ζ :=
    hasFDerivAt_of_restrictScalars ℝ h3 rfl
  refine h4.differentiableAt.congr_of_eventuallyEq ?_
  filter_upwards [hD] with ξ hξ
  exact (hξ v).symm
def tupleCoordsEquiv (b : ℕ) :
    (Fin b → ComplexVec4) ≃ₗ[ℂ] Coordinates.ComplexCoordinates (b * 4) where
  toFun ζ j := ζ (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  invFun := coordsToTuple
  map_add' a c := rfl
  map_smul' t a := rfl
  left_inv ζ := by
    funext k μ
    simp [coordsToTuple]
  right_inv z := by
    funext j
    change z (finProdFinEquiv ((finProdFinEquiv.symm j).1, (finProdFinEquiv.symm j).2)) = z j
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
def tupleCoordsCLE (b : ℕ) : (Fin b → ComplexVec4) ≃L[ℂ] Coordinates.ComplexCoordinates (b * 4) :=
  (tupleCoordsEquiv b).toContinuousLinearEquiv
theorem coordsToTuple_tupleCoordsCLE {b : ℕ} (ζ : Fin b → ComplexVec4) :
    coordsToTuple (tupleCoordsCLE b ζ) = ζ :=
  (tupleCoordsEquiv b).left_inv ζ
theorem isHolomorphicIn_of_differentiableAt {N : ℕ} {O : Set (Coordinates.ComplexCoordinates N)}
    {g : Coordinates.ComplexCoordinates N → ℂ} (hO : IsOpen O)
    (hg : ∀ z ∈ O, DifferentiableAt ℂ g z) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => g z := by
  refine ⟨hO, ?_, ?_⟩
  · exact continuousOn_pi.2 fun _ z hz => (hg z hz).continuousAt.continuousWithinAt
  · intro a ha j
    have hcont : Continuous fun t : ℂ =>
        a + t • Coordinates.ComplexCoordinates.stdBasisVector j := by fun_prop
    have hmem : ∀ᶠ t in 𝓝 (0 : ℂ), a + t • Coordinates.ComplexCoordinates.stdBasisVector j ∈ O :=
      hcont.continuousAt.eventually_mem (by simpa using hO.mem_nhds ha)
    filter_upwards [hmem] with t ht
    refine differentiableAt_pi.2 fun _ => ?_
    have hline : DifferentiableAt ℂ
        (fun t : ℂ => a + t • Coordinates.ComplexCoordinates.stdBasisVector j) t := by
      fun_prop
    exact DifferentiableAt.comp t (hg _ ht) hline
theorem tube_open_differentiable_contDiff
    (hmx : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) {b : ℕ}
    {w : (Fin b → ComplexVec4) → ℂ} (hw : IsHolomorphicOnTube (m := b) w) :
    IsOpen (tubeTuples b) ∧ (∀ ζ ∈ tubeTuples b, DifferentiableAt ℂ w ζ) ∧
      ContDiffOn ℝ 2 w (tubeTuples b) := by
  obtain ⟨-, hsm, hL, -, -⟩ := (hmx.1 (b * 4) _ hw.1).1 1 _ hw
  have hO : IsOpen (tubeTuples b) := by
    have : tubeTuples b = tupleCoordsCLE b ⁻¹' (coordsToTuple ⁻¹' tubeTuples b) := by
      ext ζ
      simp [coordsToTuple_tupleCoordsCLE]
    rw [this]
    exact hw.1.preimage (tupleCoordsCLE b).continuous
  have hw' : w = (fun z : Coordinates.ComplexCoordinates (b * 4) => w (coordsToTuple z)) ∘
      tupleCoordsCLE b := by
    funext ζ
    simp [coordsToTuple_tupleCoordsCLE]
  refine ⟨hO, ?_, ?_⟩
  · intro ζ hζ
    have hmem : tupleCoordsCLE b ζ ∈ coordsToTuple ⁻¹' tubeTuples b := by
      simpa [coordsToTuple_tupleCoordsCLE] using hζ
    obtain ⟨L, hLz⟩ := hL _ hmem
    have h1 := (hasFDerivAt_of_restrictScalars ℝ hLz rfl).differentiableAt
    have h2 := differentiableAt_pi.1 h1 0
    rw [hw']
    exact DifferentiableAt.comp ζ h2 (tupleCoordsCLE b).differentiableAt
  · have h1 := contDiffOn_pi.1 hsm 0
    rw [hw']
    refine (h1.comp ((tupleCoordsCLE b).contDiff.restrict_scalars ℝ).contDiffOn ?_).of_le
      (WithTop.coe_le_coe.2 le_top)
    intro ζ hζ
    simpa [coordsToTuple_tupleCoordsCLE] using hζ
theorem isHolomorphicOnTube_of_differentiableAt {b : ℕ} {w : (Fin b → ComplexVec4) → ℂ}
    (hO : IsOpen (tubeTuples b)) (hd : ∀ ζ ∈ tubeTuples b, DifferentiableAt ℂ w ζ) :
    IsHolomorphicOnTube (m := b) w := by
  refine isHolomorphicIn_of_differentiableAt (g := fun z => w (coordsToTuple z))
    (hO.preimage (tupleCoordsCLE b).symm.continuous) ?_
  intro z hz
  exact DifferentiableAt.comp z (hd _ hz) (tupleCoordsCLE b).symm.differentiableAt
theorem complexPartialDeriv_eq_fderiv {b : ℕ} {W : (Fin b → ComplexVec4) → ℂ}
    {ζ : Fin b → ComplexVec4} (h : DifferentiableAt ℂ W ζ) (k : Fin b) (μ : Fin 4) :
    complexPartialDeriv W k μ ζ = fderiv ℂ W ζ (Pi.single k (Pi.single μ 1)) := by
  have hp : (fun t : ℂ => Function.update ζ k (Function.update (ζ k) μ t)) =
      fun t => ζ + (t - ζ k μ) • (Pi.single k (Pi.single μ 1) : Fin b → ComplexVec4) := by
    funext t j ν
    by_cases hj : j = k
    · subst hj
      by_cases hν : ν = μ
      · subst hν
        simp
      · simp [hν]
    · simp [hj]
  have hder : HasDerivAt (fun t : ℂ => Function.update ζ k (Function.update (ζ k) μ t))
      (Pi.single k (Pi.single μ 1)) (ζ k μ) := by
    rw [hp]
    simpa using (((hasDerivAt_id (ζ k μ)).sub_const (ζ k μ)).smul_const
      (Pi.single k (Pi.single μ 1) : Fin b → ComplexVec4)).const_add ζ
  have hbase : Function.update ζ k (Function.update (ζ k) μ (ζ k μ)) = ζ := by simp
  have hW : HasFDerivAt W (fderiv ℂ W ζ)
      (Function.update ζ k (Function.update (ζ k) μ (ζ k μ))) := by
    rw [hbase]
    exact h.hasFDerivAt
  exact (hW.comp_hasDerivAt (ζ k μ) hder).deriv
theorem lieDerivative_eq_fderiv {b : ℕ} {W : (Fin b → ComplexVec4) → ℂ}
    {ζ : Fin b → ComplexVec4} (h : DifferentiableAt ℂ W ζ) (Z : ComplexMat4) :
    lieDerivative Z W ζ = fderiv ℂ W ζ (mulVecTuple Z ζ) := by
  have hv : mulVecTuple Z ζ = ∑ k, ∑ μ, (Z *ᵥ ζ k) μ •
      (Pi.single k (Pi.single μ 1) : Fin b → ComplexVec4) := by
    funext j ν
    have key : ∀ (k : Fin b) (μ : Fin 4),
        (Pi.single k (Pi.single μ 1) : Fin b → ComplexVec4) j ν =
          if k = j then (if μ = ν then 1 else 0) else 0 := by
      intro k μ
      by_cases hk : k = j
      · subst hk
        by_cases hm : μ = ν
        · subst hm
          simp
        · simp [hm, Ne.symm hm]
      · simp [hk, Ne.symm hk]
    simp only [Finset.sum_apply, Pi.smul_apply, key, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp [mulVecTuple]
  rw [hv]
  simp only [map_sum, map_smul, smul_eq_mul, lieDerivative, complexPartialDeriv_eq_fderiv h]
theorem differentiableAt_lieDerivative {b : ℕ} {W : (Fin b → ComplexVec4) → ℂ}
    {U : Set (Fin b → ComplexVec4)} (hU : IsOpen U)
    (hd : ∀ ζ ∈ U, DifferentiableAt ℂ W ζ) (hs : ContDiffOn ℝ 2 W U) (Z : ComplexMat4)
    {ζ : Fin b → ComplexVec4} (hζ : ζ ∈ U) :
    DifferentiableAt ℂ (lieDerivative Z W) ζ := by
  have hsum : DifferentiableAt ℂ (fun ξ : Fin b → ComplexVec4 => ∑ k, ∑ μ, (Z *ᵥ ξ k) μ *
      fderiv ℂ W ξ (Pi.single k (Pi.single μ 1))) ζ := by
    refine DifferentiableAt.fun_sum fun k _ => DifferentiableAt.fun_sum fun μ _ => ?_
    refine DifferentiableAt.mul ?_ (complexDifferentiableAt_fderiv_apply hU hd hs _ hζ)
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hζ] with ξ hξ
  simp only [lieDerivative, complexPartialDeriv_eq_fderiv (hd ξ hξ)]
def wickTupleCLE (b : ℕ) : (Fin b → ComplexVec4) ≃L[ℂ] (Fin b → ComplexVec4) :=
  (LinearEquiv.piCongrRight fun _ : Fin b => wickMap).toContinuousLinearEquiv
theorem eq_zero_on_tube_of_wick
    (hid : ComplexAnalysis.IdentityTheoremsProdAndUpperHalfPlane)
    (hconv : ConeTubeLorentz.ConesTubeConvex)
    (hι : ∀ x : RealVec4, wickMap (toComplex x) ∈ futureTube ↔ x 3 > 0)
    {b : ℕ} (hb : 1 ≤ b) (hO : IsOpen (tubeTuples b)) {F : (Fin b → ComplexVec4) → ℂ}
    (hF : ∀ ζ ∈ tubeTuples b, DifferentiableAt ℂ F ζ)
    (h0 : ∀ y : Fin b → RealVec4, (∀ k, 0 < y k 3) →
      F (fun k => wickMap (toComplex (y k))) = 0) :
    ∀ ζ ∈ tubeTuples b, F ζ = 0 := by
  classical
  let J : Coordinates.ComplexCoordinates (b * 4) ≃L[ℂ] (Fin b → ComplexVec4) :=
    (tupleCoordsCLE b).symm.trans (wickTupleCLE b)
  let 𝔘 : Set (Coordinates.ComplexCoordinates (b * 4) × Coordinates.ComplexCoordinates 0) :=
    {p | J p.1 ∈ tubeTuples b}
  let u : Coordinates.ComplexCoordinates (b * 4) × Coordinates.ComplexCoordinates 0 → ℂ :=
    fun p => F (J p.1)
  let y₀ : Fin b → RealVec4 := fun _ => ![0, 0, 0, 1]
  let ζ₀ : Fin b → ComplexVec4 := fun k => wickMap (toComplex (y₀ k))
  have hy₀ : ∀ k, 0 < y₀ k 3 := by
    intro k
    simp [y₀]
  have hζ₀ : ζ₀ ∈ tubeTuples b := fun k _ => (hι _).2 (hy₀ k)
  have h𝔘o : IsOpen 𝔘 := hO.preimage (J.continuous.comp continuous_fst)
  have h𝔘c : IsConnected 𝔘 := by
    have himg : 𝔘 = (fun ζ => (J.symm ζ, (0 : Coordinates.ComplexCoordinates 0))) ''
        tubeTuples b := by
      ext p
      constructor
      · intro hp
        refine ⟨J p.1, hp, ?_⟩
        refine Prod.ext (by simp) (Subsingleton.elim _ _)
      · rintro ⟨ζ, hζ, rfl⟩
        simpa [𝔘] using hζ
    rw [himg]
    have hcv : Convex ℝ (tubeTuples b) := hconv.2.2.2.2.2.2 b
    have hcont : Continuous fun ζ : Fin b → ComplexVec4 =>
        (J.symm ζ, (0 : Coordinates.ComplexCoordinates 0)) :=
      J.symm.continuous.prodMk continuous_const
    exact IsConnected.image ⟨⟨ζ₀, hζ₀⟩, hcv.isPreconnected⟩ _ hcont.continuousOn
  let S : Coordinates.ComplexCoordinates (b * 4 + 0) →L[ℂ] Coordinates.ComplexCoordinates (b * 4) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castAdd 0 i)
  have hP : ∀ z : Coordinates.ComplexCoordinates (b * 4 + 0),
      ((ComplexManifolds.coordinatesProdHomeomorph (b * 4) 0).symm z).1 = S z := by
    intro z
    rfl
  have hu : ComplexAnalysis.HolomorphicOnCoordinatesProd 𝔘 u := by
    refine isHolomorphicIn_of_differentiableAt
      (g := fun z => u ((ComplexManifolds.coordinatesProdHomeomorph (b * 4) 0).symm z))
      ((ComplexManifolds.coordinatesProdHomeomorph (b * 4) 0).isOpen_image.2 h𝔘o) ?_
    rintro z ⟨p, hp, rfl⟩
    have hfun : (fun z => u ((ComplexManifolds.coordinatesProdHomeomorph (b * 4) 0).symm z)) =
        fun z => F (J (S z)) := by
      funext z
      simp only [u, hP]
    rw [hfun]
    have hSp : S (ComplexManifolds.coordinatesProdHomeomorph (b * 4) 0 p) = p.1 := by
      rw [← hP]
      simp
    have h1 : DifferentiableAt ℂ F
        (J (S (ComplexManifolds.coordinatesProdHomeomorph (b * 4) 0 p))) := by
      rw [hSp]
      exact hF _ hp
    have h2 : DifferentiableAt ℂ (fun z => J (S z))
        (ComplexManifolds.coordinatesProdHomeomorph (b * 4) 0 p) :=
      J.differentiableAt.comp _ S.differentiableAt
    exact DifferentiableAt.comp _ h1 h2
  let 𝔵₀ : Coordinates.ComplexCoordinates (b * 4) := tupleCoordsCLE b fun k => toComplex (y₀ k)
  have hJ₀ : J 𝔵₀ = ζ₀ := by
    funext k
    change wickMap (coordsToTuple (tupleCoordsCLE b _) k) = _
    rw [coordsToTuple_tupleCoordsCLE]
  have hmem₀ : (𝔵₀, (0 : Coordinates.ComplexCoordinates 0)) ∈ 𝔘 := by
    change J 𝔵₀ ∈ tubeTuples b
    rw [hJ₀]
    exact hζ₀
  have hreal₀ : 𝔵₀ ∈ Coordinates.ComplexCoordinates.realLocus (b * 4) := by
    intro j
    change (toComplex _ _).im = 0
    simp [toComplex]
  have hev : ∀ᶠ p : Coordinates.ComplexCoordinates (b * 4) × Coordinates.ComplexCoordinates 0 in
      𝓝 (𝔵₀, (0 : Coordinates.ComplexCoordinates 0)), ∀ k, 0 < (coordsToTuple p.1 k 3).re := by
    refine Filter.eventually_all.2 fun k => ?_
    have hc : Continuous fun p : Coordinates.ComplexCoordinates (b * 4) ×
        Coordinates.ComplexCoordinates 0 => (coordsToTuple p.1 k 3).re := by
      unfold coordsToTuple
      fun_prop
    have hpos : 0 < (coordsToTuple (𝔵₀, (0 : Coordinates.ComplexCoordinates 0)).1 k 3).re := by
      change 0 < (coordsToTuple (tupleCoordsCLE b _) k 3).re
      rw [coordsToTuple_tupleCoordsCLE]
      simpa [toComplex] using hy₀ k
    exact (hc.tendsto _).eventually (lt_mem_nhds hpos)
  have hnear : ∀ᶠ p in 𝓝 (𝔵₀, (0 : Coordinates.ComplexCoordinates 0)),
      p.1 ∈ Coordinates.ComplexCoordinates.realLocus (b * 4) → u p = 0 := by
    filter_upwards [hev] with p hp hreal
    let y : Fin b → RealVec4 := fun k μ => (coordsToTuple p.1 k μ).re
    have hty : coordsToTuple p.1 = fun k => toComplex (y k) := by
      funext k μ
      refine Complex.ext ?_ ?_
      · simp [y, toComplex]
      · simpa [toComplex, coordsToTuple] using hreal (finProdFinEquiv (k, μ))
    have hJp : J p.1 = fun k => wickMap (toComplex (y k)) := by
      funext k
      change wickMap (coordsToTuple p.1 k) = _
      rw [hty]
    change F (J p.1) = 0
    rw [hJp]
    exact h0 y hp
  intro ζ hζ
  have := hid.1 (b * 4) 0 (by omega) 𝔘 u 𝔵₀ 0 h𝔘o h𝔘c hu hmem₀ hreal₀ hnear
    (J.symm ζ, 0) (by simpa [𝔘] using hζ)
  simpa [u] using this
theorem wickDiffs_eq {b : ℕ} (x : TestSpaces.PointTuple (b + 1)) (y : Fin b → RealVec4)
    (h : ∀ k : Fin b, x k.succ - x k.castSucc = y k) :
    FieldForms.wickDiffs x = fun k => wickMap (toComplex (y k)) := by
  funext k
  have hof : toComplex (y k) = toComplex (x k.succ) - toComplex (x k.castSucc) := by
    rw [← h k]
    funext μ
    simp [toComplex]
  rw [hof, map_sub]
  rfl
theorem cumulativeSums_cons_sub {b : ℕ} (y : Fin b → RealVec4) (k : Fin b) :
    cumulativeSums (Fin.cons (0 : RealVec4) y : TestSpaces.PointTuple (b + 1)) k.succ -
      cumulativeSums (Fin.cons (0 : RealVec4) y : TestSpaces.PointTuple (b + 1)) k.castSucc =
        y k := by
  have h := congrFun
    (diffCoords_cumulativeSums (Fin.cons (0 : RealVec4) y : TestSpaces.PointTuple (b + 1))) k.succ
  funext μ
  have hμ := congrFun h μ
  simp only [diffCoords, Fin.cons_succ, successiveDiffs, tupleToComplex, toComplex,
    Pi.sub_apply] at hμ
  simp only [Pi.sub_apply]
  exact_mod_cast hμ
theorem vacuumExpectation_orthogonal_invariant {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {E : FourBorelSet → BddOp K} {Ω : K}
    {A : ℝ → BddOp K} (hE : FieldForms.IsEuclidean E Ω A) {b : ℕ} (y : Fin b → RealVec4)
    (hy : ∀ k, 0 < y k 3) (R : Matrix.orthogonalGroup (Fin 4) ℝ)
    (hR : ∀ k, 0 < ((R : RealMat4) *ᵥ y k) 3) :
    FieldForms.vacuumExpectation E Ω A (b + 1)
        (fun k => wickMap (toComplex ((R : RealMat4) *ᵥ y k))) =
      FieldForms.vacuumExpectation E Ω A (b + 1) (fun k => wickMap (toComplex (y k))) := by
  set X : TestSpaces.PointTuple (b + 1) :=
    cumulativeSums (Fin.cons (0 : RealVec4) y : TestSpaces.PointTuple (b + 1)) with hX
  have hd : ∀ k : Fin b, X k.succ - X k.castSucc = y k := cumulativeSums_cons_sub y
  have hRd : ∀ k : Fin b,
      TestSpaces.rotatePermute R 1 X k.succ - TestSpaces.rotatePermute R 1 X k.castSucc =
        (R : RealMat4) *ᵥ y k := by
    intro k
    simp only [TestSpaces.rotatePermute, Equiv.Perm.coe_one, id]
    rw [← Matrix.mulVec_sub, hd k]
  have hord : ∀ (x : TestSpaces.PointTuple (b + 1)) (d : Fin b → RealVec4),
      (∀ k : Fin b, x k.succ - x k.castSucc = d k) → (∀ k, 0 < d k 3) →
      x ∈ TestSpaces.increasingTimes (b + 1) := by
    intro x d h hpos
    refine Fin.strictMono_iff_lt_succ.2 fun k => ?_
    have := hpos k
    rw [← h k] at this
    simpa [TestSpaces.timeCoord] using this
  have h := hE b X (hord X y hd hy) R 1 (hord _ _ hRd hR)
  simp only [FieldForms.orderedSchwinger] at h
  rw [wickDiffs_eq _ _ hRd, wickDiffs_eq _ _ hd] at h
  exact h
section Exponential
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
theorem hasDerivAt_exp_smul_mulVec (M : RealMat4) (y : RealVec4) :
    HasDerivAt (fun a : ℝ => NormedSpace.exp (a • M) *ᵥ y) (M *ᵥ y) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) M (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let ℓ : RealMat4 →ₗ[ℝ] RealVec4 :=
    { toFun := fun N => N *ᵥ y
      map_add' := fun N N' => Matrix.add_mulVec N N' y
      map_smul' := fun t N => Matrix.smul_mulVec t N y }
  exact (LinearMap.toContinuousLinearMap ℓ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
theorem exp_smul_mem_orthogonalGroup {M : RealMat4} (hM : Mᵀ = -M) (a : ℝ) :
    NormedSpace.exp (a • M) ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff, ← Matrix.exp_transpose, Matrix.transpose_smul, hM,
    smul_neg, Matrix.exp_neg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))
end Exponential
def wickRealCLM : RealVec4 →L[ℝ] ComplexVec4 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => wickMap (toComplex x)
      map_add' := fun x x' => by
        have : toComplex (x + x') = toComplex x + toComplex x' := by
          funext μ
          simp [toComplex]
        rw [this, map_add]
      map_smul' := fun t x => by
        have : toComplex (t • x) = (t : ℂ) • toComplex x := by
          funext μ
          simp [toComplex]
        rw [this, map_smul]
        funext μ
        simp }
theorem conjByWick_toComplexMatrix_mulVec (M : RealMat4) (y : RealVec4) :
    conjByWick (toComplexMatrix M) *ᵥ wickMap (toComplex y) =
      wickMap (toComplex (M *ᵥ y)) := by
  have h : toComplexMatrix M *ᵥ toComplex y = toComplex (M *ᵥ y) := by
    funext μ
    simp [toComplexMatrix, toComplex, Matrix.mulVec, dotProduct]
  simp only [conjByWick, LinearMap.toMatrix'_mulVec, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Matrix.mulVecLin_apply, h]
theorem fderiv_vacuumExpectation_wick_eq_zero {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {E : FourBorelSet → BddOp K} {Ω : K}
    {A : ℝ → BddOp K} (hE : FieldForms.IsEuclidean E Ω A) {b : ℕ}
    {M : RealMat4} (hM : Mᵀ = -M) (y : Fin b → RealVec4) (hy : ∀ k, 0 < y k 3)
    (hW : DifferentiableAt ℂ (FieldForms.vacuumExpectation E Ω A (b + 1))
      (fun k => wickMap (toComplex (y k)))) :
    fderiv ℂ (FieldForms.vacuumExpectation E Ω A (b + 1)) (fun k => wickMap (toComplex (y k)))
      (mulVecTuple (conjByWick (toComplexMatrix M))
        (fun k => wickMap (toComplex (y k)))) = 0 := by
  have hder : ∀ k, HasDerivAt (fun a : ℝ => NormedSpace.exp (a • M) *ᵥ y k) (M *ᵥ y k) 0 :=
    fun k => hasDerivAt_exp_smul_mulVec M (y k)
  let c : ℝ → Fin b → ComplexVec4 := fun a k =>
    wickMap (toComplex (NormedSpace.exp (a • M) *ᵥ y k))
  have hc0 : c 0 = fun k => wickMap (toComplex (y k)) := by
    funext k
    simp [c, NormedSpace.exp_zero]
  have hc : HasDerivAt c (fun k => wickMap (toComplex (M *ᵥ y k))) 0 :=
    hasDerivAt_pi.2 fun k =>
      wickRealCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hder k)
  have hpos : ∀ᶠ a in 𝓝 (0 : ℝ), ∀ k, 0 < (NormedSpace.exp (a • M) *ᵥ y k) 3 := by
    refine Filter.eventually_all.2 fun k => ?_
    have hcont : ContinuousAt (fun a : ℝ => (NormedSpace.exp (a • M) *ᵥ y k) 3) 0 :=
      (continuous_apply 3).continuousAt.comp (hder k).continuousAt
    refine hcont.eventually (lt_mem_nhds ?_)
    simpa [NormedSpace.exp_zero] using hy k
  have hconst : (FieldForms.vacuumExpectation E Ω A (b + 1)) ∘ c =ᶠ[𝓝 0]
      fun _ => FieldForms.vacuumExpectation E Ω A (b + 1) (c 0) := by
    filter_upwards [hpos] with a ha
    rw [hc0]
    exact vacuumExpectation_orthogonal_invariant hE y hy ⟨_, exp_smul_mem_orthogonalGroup hM a⟩ ha
  have h1 : HasDerivAt ((FieldForms.vacuumExpectation E Ω A (b + 1)) ∘ c) 0 0 :=
    (hasDerivAt_const (0 : ℝ) _).congr_of_eventuallyEq hconst
  have hW' : HasFDerivAt (FieldForms.vacuumExpectation E Ω A (b + 1))
      ((fderiv ℂ (FieldForms.vacuumExpectation E Ω A (b + 1))
        (fun k => wickMap (toComplex (y k)))).restrictScalars ℝ) (c 0) := by
    rw [hc0]
    exact hW.hasFDerivAt.restrictScalars ℝ
  have h2 := hW'.comp_hasDerivAt (0 : ℝ) hc
  have h3 := h2.unique h1
  have hv : mulVecTuple (conjByWick (toComplexMatrix M))
      (fun k => wickMap (toComplex (y k))) =
      fun k => wickMap (toComplex (M *ᵥ y k)) := by
    funext k
    exact conjByWick_toComplexMatrix_mulVec M (y k)
  exact (congrArg (fderiv ℂ (FieldForms.vacuumExpectation E Ω A (b + 1))
    (fun k => wickMap (toComplex (y k)))) hv).trans h3
theorem eq_of_lorentz_path {b : ℕ} {W : (Fin b → ComplexVec4) → ℂ}
    (hinv : ∀ Λ ∈ lorentzGroupC, IsUnit Λ)
    (hd : ∀ ζ ∈ tubeTuples b, DifferentiableAt ℂ W ζ)
    (hvan : ∀ Z ∈ lorentzAlgebraC, ∀ ζ ∈ tubeTuples b,
      fderiv ℂ W ζ (mulVecTuple Z ζ) = 0)
    (Λ : ℝ → ComplexMat4) (ζ : Fin b → ComplexVec4)
    (h1 : ∀ t ∈ Icc (0 : ℝ) 1, Λ t ∈ lorentzGroupC)
    (h2 : ∀ i j, ContDiffOn ℝ 1 (fun t => Λ t i j) (Icc (0 : ℝ) 1))
    (h3 : ∀ t ∈ Icc (0 : ℝ) 1, mulVecTuple (Λ t) ζ ∈ tubeTuples b) :
    W (mulVecTuple (Λ 1) ζ) = W (mulVecTuple (Λ 0) ζ) := by
  let D : ℝ → ComplexMat4 := fun t =>
    Matrix.of fun i j => derivWithin (fun s => Λ s i j) (Icc (0 : ℝ) 1) t
  have hentry : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j,
      HasDerivWithinAt (fun s => Λ s i j) (D t i j) (Icc (0 : ℝ) 1) t := fun t ht i j =>
    ((h2 i j).differentiableOn (by norm_num) t ht).hasDerivWithinAt
  have hvec : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : ComplexVec4,
      HasDerivWithinAt (fun s => Λ s *ᵥ u) (D t *ᵥ u) (Icc (0 : ℝ) 1) t := by
    intro t ht u
    refine hasDerivWithinAt_pi.2 fun μ => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact HasDerivWithinAt.fun_sum fun ν _ => (hentry t ht μ ν).mul_const (u ν)
  have hform : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u v : ComplexVec4,
      minkowskiForm (D t *ᵥ u) (Λ t *ᵥ v) + minkowskiForm (Λ t *ᵥ u) (D t *ᵥ v) = 0 := by
    intro t ht u v
    have hc : ∀ μ ν : Fin 4, HasDerivWithinAt (fun s => (Λ s *ᵥ u) μ * (Λ s *ᵥ v) ν)
        ((D t *ᵥ u) μ * (Λ t *ᵥ v) ν + (Λ t *ᵥ u) μ * (D t *ᵥ v) ν) (Icc (0 : ℝ) 1) t :=
      fun μ ν => (hasDerivWithinAt_pi.1 (hvec t ht u) μ).fun_mul
        (hasDerivWithinAt_pi.1 (hvec t ht v) ν)
    have hf : HasDerivWithinAt (fun s => minkowskiForm (Λ s *ᵥ u) (Λ s *ᵥ v))
        (minkowskiForm (D t *ᵥ u) (Λ t *ᵥ v) + minkowskiForm (Λ t *ᵥ u) (D t *ᵥ v))
        (Icc (0 : ℝ) 1) t := by
      simp only [minkowskiForm, spaceBilin, spacePart, Fin.sum_univ_three]
      refine ((hc 0 0).fun_sub (((hc (Fin.succ 0) (Fin.succ 0)).fun_add
        (hc (Fin.succ 1) (Fin.succ 1))).fun_add (hc (Fin.succ 2) (Fin.succ 2)))).congr_deriv ?_
      ring
    have hk : HasDerivWithinAt (fun s => minkowskiForm (Λ s *ᵥ u) (Λ s *ᵥ v)) 0
        (Icc (0 : ℝ) 1) t :=
      (hasDerivWithinAt_const t _ (minkowskiForm u v)).congr (fun s hs => h1 s hs u v)
        (h1 t ht u v)
    exact (uniqueDiffOn_Icc zero_lt_one t ht).eq_deriv _ hf hk
  have hΛ : ∀ t ∈ Icc (0 : ℝ) 1, Λ t * (Λ t)⁻¹ = 1 := fun t ht =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (hinv _ (h1 t ht)))
  have hΛ' : ∀ t ∈ Icc (0 : ℝ) 1, (Λ t)⁻¹ * Λ t = 1 := fun t ht =>
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hinv _ (h1 t ht)))
  have hZ : ∀ t ∈ Icc (0 : ℝ) 1, D t * (Λ t)⁻¹ ∈ lorentzAlgebraC := by
    intro t ht
    change ∀ ζ' ζ'' : ComplexVec4, minkowskiForm ((D t * (Λ t)⁻¹) *ᵥ ζ') ζ'' +
      minkowskiForm ζ' ((D t * (Λ t)⁻¹) *ᵥ ζ'') = 0
    intro ζ' ζ''
    have hback : ∀ w : ComplexVec4, Λ t *ᵥ ((Λ t)⁻¹ *ᵥ w) = w := by
      intro w
      rw [Matrix.mulVec_mulVec, hΛ t ht, Matrix.one_mulVec]
    have h := hform t ht ((Λ t)⁻¹ *ᵥ ζ') ((Λ t)⁻¹ *ᵥ ζ'')
    rw [hback, hback, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h
    exact h
  have hcurve : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s => mulVecTuple (Λ s) ζ)
      (mulVecTuple (D t) ζ) (Icc (0 : ℝ) 1) t := fun t ht =>
    hasDerivWithinAt_pi.2 fun k => hvec t ht (ζ k)
  have hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s => W (mulVecTuple (Λ s) ζ)) 0
      (Icc (0 : ℝ) 1) t := by
    intro t ht
    have hW := (hd _ (h3 t ht)).hasFDerivAt.restrictScalars ℝ
    have h := hW.comp_hasDerivWithinAt t (hcurve t ht)
    have hzero : fderiv ℂ W (mulVecTuple (Λ t) ζ) (mulVecTuple (D t) ζ) = 0 := by
      have h0 := hvan _ (hZ t ht) _ (h3 t ht)
      have e : mulVecTuple (D t * (Λ t)⁻¹) (mulVecTuple (Λ t) ζ) = mulVecTuple (D t) ζ := by
        funext k
        simp only [mulVecTuple]
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hΛ' t ht, Matrix.mul_one]
      rwa [e] at h0
    exact h.congr_deriv hzero
  exact constant_of_derivWithin_zero (fun t ht => (hf t ht).differentiableWithinAt)
    (fun t ht => (hf t ⟨ht.1, ht.2.le⟩).derivWithin
      (uniqueDiffOn_Icc zero_lt_one t ⟨ht.1, ht.2.le⟩))
    1 ⟨zero_le_one, le_rfl⟩
def mulVecTupleCLM (b : ℕ) (M : ComplexMat4) :
    (Fin b → ComplexVec4) →L[ℂ] (Fin b → ComplexVec4) :=
  LinearMap.toContinuousLinearMap
    { toFun := mulVecTuple M
      map_add' := fun a c => by
        funext k
        simp [mulVecTuple, Matrix.mulVec_add]
      map_smul' := fun t a => by
        funext k
        simp [mulVecTuple, Matrix.mulVec_smul] }
theorem rotationSumOne_mem_orthogonalGroup (R : Matrix.orthogonalGroup (Fin 3) ℝ) :
    rotationSumOne R ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  have hR : (R : Matrix (Fin 3) (Fin 3) ℝ) * (R : Matrix (Fin 3) (Fin 3) ℝ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).1 R.2
  rw [Matrix.mem_orthogonalGroup_iff]
  unfold rotationSumOne
  simp only [Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [hR]
theorem invariant_rotationMatrix {b : ℕ} {W : (Fin b → ComplexVec4) → ℂ}
    (hE : ∀ (y : Fin b → RealVec4) (R : Matrix.orthogonalGroup (Fin 4) ℝ), (∀ k, 0 < y k 3) →
      (∀ k, 0 < ((R : RealMat4) *ᵥ y k) 3) →
      W (fun k => wickMap (toComplex ((R : RealMat4) *ᵥ y k))) =
        W (fun k => wickMap (toComplex (y k))))
    (hid : ComplexAnalysis.IdentityTheoremsProdAndUpperHalfPlane)
    (hconv : ConeTubeLorentz.ConesTubeConvex)
    (hι : ∀ x : RealVec4, wickMap (toComplex x) ∈ futureTube ↔ x 3 > 0)
    (hb : 1 ≤ b) (hO : IsOpen (tubeTuples b))
    (hd : ∀ ζ ∈ tubeTuples b, DifferentiableAt ℂ W ζ)
    (R : Matrix.orthogonalGroup (Fin 3) ℝ)
    (hconj : conjByWick (toComplexMatrix (rotationSumOne R)) = rotationMatrix R)
    (htube : ∀ ζ ∈ futureTube, rotationMatrix R *ᵥ ζ ∈ futureTube) :
    ∀ ζ ∈ tubeTuples b, W (mulVecTuple (rotationMatrix R) ζ) = W ζ := by
  have hmaps : ∀ ζ ∈ tubeTuples b, mulVecTuple (rotationMatrix R) ζ ∈ tubeTuples b :=
    fun ζ hζ k _ => htube _ (hζ k (Set.mem_univ k))
  have hF : ∀ ζ ∈ tubeTuples b, DifferentiableAt ℂ (fun ζ =>
      W (mulVecTuple (rotationMatrix R) ζ) - W ζ) ζ := by
    intro ζ hζ
    have h1 : DifferentiableAt ℂ (fun ζ => W (mulVecTupleCLM b (rotationMatrix R) ζ)) ζ :=
      DifferentiableAt.comp ζ (hd _ (hmaps ζ hζ))
        (mulVecTupleCLM b (rotationMatrix R)).differentiableAt
    exact h1.fun_sub (hd ζ hζ)
  have h0 : ∀ y : Fin b → RealVec4, (∀ k, 0 < y k 3) →
      W (mulVecTuple (rotationMatrix R) fun k => wickMap (toComplex (y k))) -
        W (fun k => wickMap (toComplex (y k))) = 0 := by
    intro y hy
    have hact : ∀ x : RealVec4, rotationMatrix R *ᵥ wickMap (toComplex x) =
        wickMap (toComplex (rotationSumOne R *ᵥ x)) := by
      intro x
      rw [← hconj, conjByWick_toComplexMatrix_mulVec]
    have htime : ∀ x : RealVec4, (rotationSumOne R *ᵥ x) 3 = x 3 := by
      intro x
      have h := congrFun (hact x) 0
      rw [rotationMatrix_mulVec, wickMap_apply_zero] at h
      have h' : wickMap (toComplex x) 0 =
          Complex.I * toComplex (rotationSumOne R *ᵥ x) 3 := h
      rw [wickMap_apply_zero] at h'
      have h'' := mul_left_cancel₀ Complex.I_ne_zero h'
      simpa [toComplex] using h''.symm
    have hrot := hE y ⟨_, rotationSumOne_mem_orthogonalGroup R⟩ hy
      (fun k => by simpa [htime] using hy k)
    have he : (mulVecTuple (rotationMatrix R) fun k => wickMap (toComplex (y k))) =
        fun k => wickMap (toComplex (rotationSumOne R *ᵥ y k)) := by
      funext k
      exact hact (y k)
    rw [he]
    exact sub_eq_zero.2 hrot
  intro ζ hζ
  exact sub_eq_zero.1 (eq_zero_on_tube_of_wick hid hconv hι hb hO hF h0 ζ hζ)
theorem boostMatrix_zero (v : unitSphere3) : boostMatrix v 0 = 1 := by
  have h : boostLinearMap v 0 = LinearMap.id := LinearMap.ext fun ζ => by simp [boostLinearMap]
  simp [boostMatrix, h]
theorem contDiff_boostMatrix_entry (v : unitSphere3) (β : ℝ) (i j : Fin 4) :
    ContDiff ℝ 1 (fun t : ℝ => boostMatrix v ((t * β : ℝ) : ℂ) i j) := by
  let ζ : ComplexVec4 := Pi.single j 1
  have e : ∀ c : ℂ, boostMatrix v c i j = ζ i +
      (Complex.cosh c - 1) * (ζ 0 * toComplex timeUnit i + axisDot v ζ * toComplex (ofSpaceVector v) i) +
      Complex.sinh c * (axisDot v ζ * toComplex timeUnit i + ζ 0 * toComplex (ofSpaceVector v) i) := by
    intro c
    have h : boostMatrix v c i j = (boostMatrix v c *ᵥ ζ) i := by
      simp [ζ]
    rw [h, boostMatrix_mulVec]
    rfl
  simp only [e]
  have harg : ContDiff ℝ 1 (fun t : ℝ => ((t * β : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_id.mul contDiff_const)
  have hcosh : ContDiff ℝ 1 (fun t : ℝ => Complex.cosh ((t * β : ℝ) : ℂ)) :=
    (Complex.contDiff_cosh.restrict_scalars ℝ).comp harg
  have hsinh : ContDiff ℝ 1 (fun t : ℝ => Complex.sinh ((t * β : ℝ) : ℂ)) :=
    (Complex.contDiff_sinh.restrict_scalars ℝ).comp harg
  exact (contDiff_const.add ((hcosh.sub contDiff_const).mul contDiff_const)).add
    (hsinh.mul contDiff_const)
theorem invariant_boostMatrix {b : ℕ} {W : (Fin b → ComplexVec4) → ℂ}
    (hinv : ∀ Λ ∈ lorentzGroupC, IsUnit Λ)
    (hd : ∀ ζ ∈ tubeTuples b, DifferentiableAt ℂ W ζ)
    (hvan : ∀ Z ∈ lorentzAlgebraC, ∀ ζ ∈ tubeTuples b,
      fderiv ℂ W ζ (mulVecTuple Z ζ) = 0)
    (hL : ∀ (v : unitSphere3) (c : ℂ), boostMatrix v c ∈ lorentzGroupC)
    (htube : ∀ (β : ℝ), ∀ ζ ∈ futureTube, boostMatrix spaceAxisOne (β : ℂ) *ᵥ ζ ∈ futureTube)
    (β : ℝ) (ζ : Fin b → ComplexVec4) (hζ : ζ ∈ tubeTuples b) :
    W (mulVecTuple (boostMatrix spaceAxisOne (β : ℂ)) ζ) = W ζ := by
  have h := eq_of_lorentz_path hinv hd hvan
    (fun t => boostMatrix spaceAxisOne ((t * β : ℝ) : ℂ)) ζ (fun _ _ => hL _ _)
    (fun i j => (contDiff_boostMatrix_entry spaceAxisOne β i j).contDiffOn)
    (fun t _ k _ => htube _ _ (hζ k (Set.mem_univ k)))
  have h1 : mulVecTuple (1 : ComplexMat4) ζ = ζ := by
    funext k
    simp [mulVecTuple]
  simpa [boostMatrix_zero, h1] using h
theorem mulVecTuple_matrix_add {b : ℕ} (M N : ComplexMat4) (ζ : Fin b → ComplexVec4) :
    mulVecTuple (M + N) ζ = mulVecTuple M ζ + mulVecTuple N ζ := by
  funext k
  simp [mulVecTuple, Matrix.add_mulVec]
theorem mulVecTuple_matrix_smul {b : ℕ} (c : ℂ) (M : ComplexMat4) (ζ : Fin b → ComplexVec4) :
    mulVecTuple (c • M) ζ = c • mulVecTuple M ζ := by
  funext k
  simp [mulVecTuple, Matrix.smul_mulVec]
theorem mulVecTuple_matrix_mul {b : ℕ} (M N : ComplexMat4) (ζ : Fin b → ComplexVec4) :
    mulVecTuple (M * N) ζ = mulVecTuple M (mulVecTuple N ζ) := by
  funext k
  simp [mulVecTuple, Matrix.mulVec_mulVec]
theorem fderiv_mulVecTuple_eq_zero
    (hid : ComplexAnalysis.IdentityTheoremsProdAndUpperHalfPlane)
    (hconv : ConeTubeLorentz.ConesTubeConvex)
    (hι : ∀ x : RealVec4, wickMap (toComplex x) ∈ futureTube ↔ x 3 > 0)
    (hspan : lorentzAlgebraC = Submodule.span ℂ
      {Z | ∃ A : RealMat4, Aᵀ = -A ∧ Z = conjByWick (toComplexMatrix A)})
    {b : ℕ} {W : (Fin b → ComplexVec4) → ℂ} (hb : 1 ≤ b) (hO : IsOpen (tubeTuples b))
    (hd : ∀ ζ ∈ tubeTuples b, DifferentiableAt ℂ W ζ) (hs : ContDiffOn ℝ 2 W (tubeTuples b))
    (hM : ∀ M : RealMat4, Mᵀ = -M → ∀ y : Fin b → RealVec4, (∀ k, 0 < y k 3) →
      fderiv ℂ W (fun k => wickMap (toComplex (y k)))
        (mulVecTuple (conjByWick (toComplexMatrix M))
          (fun k => wickMap (toComplex (y k)))) = 0) :
    ∀ Z ∈ lorentzAlgebraC, ∀ ζ ∈ tubeTuples b,
      fderiv ℂ W ζ (mulVecTuple Z ζ) = 0 := by
  intro Z hZ
  have h0 : ∀ y : Fin b → RealVec4, (∀ k, 0 < y k 3) →
      lieDerivative Z W (fun k => wickMap (toComplex (y k))) = 0 := by
    intro y hy
    rw [lieDerivative_eq_fderiv (hd _ fun k _ => (hι _).2 (hy k))]
    rw [hspan] at hZ
    induction hZ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨M, hMa, rfl⟩ := hx
      exact hM M hMa y hy
    | zero =>
      have : mulVecTuple (0 : ComplexMat4)
          (fun k => wickMap (toComplex (y k))) = 0 := by
        funext k
        simp [mulVecTuple]
      rw [this, map_zero]
    | add x x' _ _ hx hx' =>
      rw [mulVecTuple_matrix_add, map_add, hx, hx', add_zero]
    | smul c x _ hx =>
      rw [mulVecTuple_matrix_smul, map_smul, hx, smul_zero]
  have hall := eq_zero_on_tube_of_wick hid hconv hι hb hO
    (fun ζ hζ => differentiableAt_lieDerivative hO hd hs Z hζ) h0
  intro ζ hζ
  rw [← lieDerivative_eq_fderiv (hd ζ hζ)]
  exact hall ζ hζ
theorem statement_holds (hcone : MinkowskiSpace.ConeTubeLorentz.Statement)
    (hprod : FieldForms.FieldProductProperties)
    (hid : ComplexAnalysis.IdentityTheoremsProdAndUpperHalfPlane)
    (hmx : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) : Statement := by
  intro K _ _ _ E Ω A ℘ C hform hE b hb
  obtain ⟨-, hconv, -, hF, hB, -, hReal, hDec, hGrp, hCL, -, -⟩ := hcone
  have hW0 : IsHolomorphicOnTube (m := b) (FieldForms.vacuumExpectation E Ω A (b + 1)) :=
    ((hprod K E Ω A ℘ C hform).2.2.2.2.2.2.2.1 b).1
  obtain ⟨hO, hd, hs⟩ := tube_open_differentiable_contDiff hmx hW0
  have hι := hF.2.2.2.2.2.1
  have hspan := hF.2.2.2.1
  have hconjR := hF.2.2.2.2.2.2.2
  have hmemι : ∀ y : Fin b → RealVec4, (∀ k, 0 < y k 3) →
      (fun k => wickMap (toComplex (y k))) ∈ tubeTuples b :=
    fun y hy k _ => (hι _).2 (hy k)
  have hvan : ∀ Z ∈ lorentzAlgebraC, ∀ ζ ∈ tubeTuples b,
      fderiv ℂ (FieldForms.vacuumExpectation E Ω A (b + 1)) ζ (mulVecTuple Z ζ) = 0 :=
    fderiv_mulVecTuple_eq_zero hid hconv hι hspan hb hO hd hs fun M hM y hy =>
      fderiv_vacuumExpectation_wick_eq_zero hE hM y hy (hd _ (hmemι y hy))
  have hPO : ∀ Λ ∈ restrictedLorentz, ∀ ζ ∈ futureTube, toComplexMatrix Λ *ᵥ ζ ∈ futureTube := by
    intro Λ hΛ ζ hζ
    rw [← (hGrp.2 Λ hΛ).2.2.1]
    exact ⟨ζ, hζ, rfl⟩
  have hRtube : ∀ R : Matrix.orthogonalGroup (Fin 3) ℝ, (R : Matrix (Fin 3) (Fin 3) ℝ).det = 1 →
      ∀ ζ ∈ futureTube, rotationMatrix R *ᵥ ζ ∈ futureTube := by
    intro R hR ζ hζ
    obtain ⟨Λ, hΛ, he, -⟩ := hReal.2 R hR
    rw [← he]
    exact hPO Λ hΛ ζ hζ
  have hBtube : ∀ (β : ℝ), ∀ ζ ∈ futureTube,
      boostMatrix spaceAxisOne (β : ℂ) *ᵥ ζ ∈ futureTube := by
    intro β ζ hζ
    obtain ⟨Λ, hΛ, he, -⟩ := hReal.1 spaceAxisOne β
    rw [← he]
    exact hPO Λ hΛ ζ hζ
  have hrot : ∀ R : Matrix.orthogonalGroup (Fin 3) ℝ, (R : Matrix (Fin 3) (Fin 3) ℝ).det = 1 →
      ∀ ζ ∈ tubeTuples b, FieldForms.vacuumExpectation E Ω A (b + 1)
          (mulVecTuple (rotationMatrix R) ζ) =
        FieldForms.vacuumExpectation E Ω A (b + 1) ζ := fun R hR =>
    invariant_rotationMatrix
      (fun y R' hy hR' => vacuumExpectation_orthogonal_invariant hE y hy R' hR') hid hconv hι
      hb hO hd R (hconjR R) (hRtube R hR)
  refine ⟨fun Z hZ => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact isHolomorphicOnTube_of_differentiableAt hO
      fun ζ hζ => differentiableAt_lieDerivative hO hd hs Z hζ
  · intro ζ hζ
    exact (lieDerivative_eq_fderiv (b := b) (hd ζ hζ) Z).trans (hvan Z hZ ζ hζ)
  · intro Λ ζ h1 h2 h3
    exact eq_of_lorentz_path hCL.1 hd hvan Λ ζ h1 h2 h3
  · intro Λ hΛ ζ hζ
    obtain ⟨R₁, R₂, β, h₁, h₂, -, hdec⟩ := hDec Λ hΛ
    have hζ₂ : mulVecTuple (rotationMatrix R₂) ζ ∈ tubeTuples b :=
      fun k _ => hRtube R₂ h₂ _ (hζ k (Set.mem_univ k))
    have hζ₁ : mulVecTuple (boostMatrix spaceAxisOne (β : ℂ))
        (mulVecTuple (rotationMatrix R₂) ζ) ∈ tubeTuples b :=
      fun k _ => hBtube β _ (hζ₂ k (Set.mem_univ k))
    rw [hdec, mulVecTuple_matrix_mul, mulVecTuple_matrix_mul, hrot R₁ h₁ _ hζ₁,
      invariant_boostMatrix hCL.1 hd hvan hB.1 hBtube β _ hζ₂, hrot R₂ h₂ _ hζ]
end YangMills.Construction.VacuumLorentzInvariance
