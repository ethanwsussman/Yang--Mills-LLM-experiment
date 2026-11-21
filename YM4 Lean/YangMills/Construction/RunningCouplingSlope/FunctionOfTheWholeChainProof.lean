import YangMills.Construction.RunningCouplingSlope.ChainIsOneGaussianNumber
import YangMills.Construction.RunningCouplingSlope.CovarianceOfTheFunctionOfTheWholeChainProof
import YangMills.Construction.RunningCouplingSlope.FibreFormAtALeastPoint
import YangMills.Construction.RunningCouplingSlope.FlatPointIsLeast
import YangMills.Construction.RunningCouplingSlope.FormAfterTheChangeOfGauge
import YangMills.Construction.RunningCouplingSlope.FunctionOfTheWholeChain
import YangMills.Construction.RunningCouplingSlope.GhostAndFormAtALeastPoint
import YangMills.Construction.RunningCouplingSlope.GradientAtTheFlatPoint
import YangMills.Construction.RunningCouplingSlope.GradientsAtALeastPoint
import YangMills.Construction.RunningCouplingSlope.MapsOfTheChainAtALeastPoint
import YangMills.Construction.RunningCouplingSlope.NumberOfAnOrbitThroughTwoDeterminants
import YangMills.Construction.RunningCouplingSlope.TheGaugeShiftReadsNearCellsProof
import YangMills.Construction.RunningCouplingSlope.TheKernelOfTheHessianOfTheWholeChainDecaysProof
import YangMills.Construction.Towers.SecondDifferentialAtACriticalPointProof
import YangMills.Construction.Towers.TheSaddleDeterminantProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.ChainFreeEnergyAnalytic
open Filter Module Tower LinearConstraint GaussianConstraint Matrices
open scoped Topology
variable {L n k : ℕ}
private theorem formValues_injective : Function.Injective (formValues (L := L) (m := n) (k := k)) := by apply _root_.YangMills.SharedProofs.p13252 <;> assumption
private theorem levelFormsEuclidean_of (hF : FiniteSideFormSpaces)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) : LevelFormsEuclidean L n k := by apply _root_.YangMills.SharedProofs.p14283 <;> assumption
private theorem exists_symmetric_operator_of_quadratic {A : Type} [AddCommGroup A] [Module ℝ A]
    [FiniteDimensional ℝ A] (c : InnerProductSpace.Core ℝ A) (q : QuadraticForm ℝ A) :
    ∃ T : A →ₗ[ℝ] A, (∀ x y, c.inner x (T y) = c.inner (T x) y) ∧ ∀ x, c.inner x (T x) = q x := by
  classical
  let := c.toNormedAddCommGroup
  let := InnerProductSpace.ofCore c.toCore
  let β := QuadraticMap.associated (R := ℝ) q
  let b := stdOrthonormalBasis ℝ A
  let Y : A →ₗ[ℝ] A := ∑ i, (β.flip (b i)).smulRight (b i)
  have hY : ∀ x y : A, inner ℝ (Y x) y = β x y := by
    intro x y
    have hy : y = ∑ i, (inner ℝ (b i) y) • b i := (b.sum_repr' y).symm
    conv_rhs => rw [hy]
    simp only [Y, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.flip_apply, map_sum,
      map_smul, sum_inner, inner_smul_left, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  have hsym : ∀ x y, β x y = β y x := fun x y => QuadraticMap.associated_isSymm ℝ q x y
  refine ⟨Y, fun x y => ?_, fun x => ?_⟩
  · show inner ℝ x (Y y) = inner ℝ (Y x) y
    rw [real_inner_comm, hY, hY, hsym]
  · show inner ℝ x (Y x) = q x
    rw [real_inner_comm, hY]
    exact QuadraticMap.associated_eq_self_apply ℝ q x
section Cores
variable {A C G Gc Y : Type} [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A]
  [AddCommGroup C] [Module ℝ C] [FiniteDimensional ℝ C]
  [AddCommGroup G] [Module ℝ G] [FiniteDimensional ℝ G]
  [AddCommGroup Gc] [Module ℝ Gc] [FiniteDimensional ℝ Gc]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
private theorem gaussianNumber_through_cores (hN : GaussianNumberViaBorderedDeterminant)
    (cA : InnerProductSpace.Core ℝ A) (cC : InnerProductSpace.Core ℝ C)
    (cG : InnerProductSpace.Core ℝ G) (cGc : InnerProductSpace.Core ℝ Gc)
    (D : G →ₗ[ℝ] A) (Dc : Gc →ₗ[ℝ] C) (Q Q' : A →ₗ[ℝ] C) (r r₂ aa : G →ₗ[ℝ] Gc) (n₀ : A →ₗ[ℝ] Gc)
    (p : A →ₗ[ℝ] G) (rt t₁ t₂ : Gc →ₗ[ℝ] G) (b : ℝ) (T : QuadraticForm ℝ (LinearMap.ker Q))
    (X : A →ₗ[ℝ] A) (l : A →ₗ[ℝ] Y) (K : Submodule ℝ G) (hK : K = LinearMap.ker r)
    (hQ : Function.Surjective Q)
    (hrt : ∀ g x, cG.inner (rt g) x = cGc.inner g (r x))
    (hrrt : ∀ g, r (rt g) = g)
    (hQD : ∀ x, Q (D x) = Dc (r x))
    (hb : 0 < b)
    (haa : ∀ x, aa x = r x + n₀ (D x))
    (hQ' : ∀ ξ, Q' ξ = Q ξ + Dc (n₀ ξ))
    (ht₁ : ∀ g x, cG.inner (t₁ g) x = cGc.inner g (aa x))
    (haat₁ : ∀ g, aa (t₁ g) = b • g)
    (haart : ∀ g, aa (rt g) = b • g)
    (ht₂ : ∀ g x, cG.inner (t₂ g) x = cGc.inner g (r₂ x))
    (hr₂t₂ : ∀ g, r₂ (t₂ g) = b • g)
    (hDinj : Function.Injective (D ∘ₗ K.subtype))
    (hT0 : ∀ ξ, 0 ≤ T ξ)
    (hTnull : ∀ ξ : LinearMap.ker Q, T ξ = 0 ↔ (ξ : A) ∈ K.map D)
    (hghost : LinearMap.det (borderedBlockOperator (p ∘ₗ D) t₂ aa) ≠ 0)
    (hXs : ∀ x y, cA.inner x (X y) = cA.inner (X x) y)
    (hXf : ∀ ξ, Q' ξ = 0 → ∀ h : ξ + D (rt (n₀ ξ)) ∈ LinearMap.ker Q,
      cA.inner ξ (X ξ) = T ⟨_, h⟩ +
        cG.inner (p ξ - b⁻¹ • t₂ (r₂ (p ξ))) (p ξ - b⁻¹ • t₂ (r₂ (p ξ))))
    (hl : Function.Bijective (l ∘ₗ D ∘ₗ K.subtype)) :
    saddleDetOfCores cA cC X Q' ≠ 0 ∧
      constrainedGaussianNumberOfCores cA cC Q (T + (normSqForm l).comp (LinearMap.ker Q).subtype) *
        (letI := cG.toNormedAddCommGroup
         letI := InnerProductSpace.ofCore cG.toCore
         absDetOfMap (l ∘ₗ D ∘ₗ K.subtype)) =
      (b ^ finrank ℝ Gc) ^ (1 / 2 : ℝ) * (b ^ finrank ℝ Gc)⁻¹ *
        (2 * Real.pi) ^ (((finrank ℝ A : ℝ) - (finrank ℝ C : ℝ)) / 2) *
        |saddleDetOfCores cA cC X Q'| ^ (-(1 / 2) : ℝ) *
        |LinearMap.det (borderedBlockOperator (p ∘ₗ D) t₂ aa)| := by
  subst hK
  let := cA.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cA.toCore
  let := cC.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cC.toCore
  let := cG.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cG.toCore
  let := cGc.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cGc.toCore
  have adjr : LinearMap.adjoint r = rt := ((LinearMap.eq_adjoint_iff rt r).mpr hrt).symm
  have adj₁ : LinearMap.adjoint aa = t₁ := ((LinearMap.eq_adjoint_iff t₁ aa).mpr ht₁).symm
  have adj₂ : LinearMap.adjoint r₂ = t₂ := ((LinearMap.eq_adjoint_iff t₂ r₂).mpr ht₂).symm
  have haaeq : r + n₀ ∘ₗ D = aa := LinearMap.ext fun x => (haa x).symm
  have hQeq : Q + Dc ∘ₗ n₀ = Q' := LinearMap.ext fun ξ => (hQ' ξ).symm
  have key := hN G A Gc C Y D Dc Q r r₂ n₀ p b T X l hQ
    (LinearMap.ext fun g => by rw [adjr]; exact hrrt g) (LinearMap.ext hQD) hb
    (by rw [haaeq, adj₁]; exact LinearMap.ext haat₁)
    (by rw [haaeq, adjr]; exact LinearMap.ext haart)
    (by rw [adj₂]; exact LinearMap.ext hr₂t₂)
    hDinj hT0 hTnull (by rw [adj₂, haaeq]; exact hghost) (fun x y => (hXs x y).symm)
    (fun ξ hξ h => by
      rw [hQeq] at hξ
      have h' : ξ + D (rt (n₀ ξ)) ∈ LinearMap.ker Q := by rwa [adjr] at h
      have e : (⟨_, h⟩ : LinearMap.ker Q) = ⟨_, h'⟩ := Subtype.ext (by simp only [adjr])
      rw [e, adj₂, ← real_inner_self_eq_norm_sq]
      exact hXf ξ hξ h')
    hl
  rw [hQeq, haaeq, adj₂] at key
  exact key
end Cores
private def towerLogConstant (L n k : ℕ) : ℝ :=
  Real.log ((((((L : ℝ) ^ (4 * k))⁻¹) ^ finrank ℝ (vertexFunctionSpace L n k k)) ^ (1 / 2 : ℝ)) *
    ((((L : ℝ) ^ (4 * k))⁻¹) ^ finrank ℝ (vertexFunctionSpace L n k k))⁻¹ *
    (2 * Real.pi) ^ (((finrank ℝ (LevelForms L n k) : ℝ) - (finrank ℝ (edgeFormSpace L n k k) : ℝ)) / 2))
private theorem log_mul_rpow_abs (c s t : ℝ) (hc : 0 < c) (hs : s ≠ 0) (ht : t ≠ 0) :
    Real.log (c * |s| ^ (-(1 / 2) : ℝ) * |t|) =
      Real.log c - (1 / 2) * Real.log |s| + Real.log |t| := by
  have hs' : 0 < |s| := abs_pos.mpr hs
  have ht' : 0 < |t| := abs_pos.mpr ht
  rw [Real.log_mul (by positivity) ht'.ne', Real.log_mul hc.ne' (by positivity),
    Real.log_rpow hs']
  ring
private theorem gaugedOperator_spec {a : ℝ} (hA : LevelFormsEuclidean L n k)
    {X : ChainPoint L n k} {J : LevelForms L n k} {μ : edgeFormSpace L n k k}
    (q : QuadraticForm ℝ (LevelForms L n k)) (hq : ∀ ξ, q ξ = gaugedRightValue a X J μ ξ) :
    IsGaugedOperator a X J μ (gaugedOperator a X J μ) := by
  haveI := hA.1
  obtain ⟨c, hc⟩ := hA.2
  obtain ⟨T, hs, hf⟩ := exists_symmetric_operator_of_quadratic c q
  refine Classical.epsilon_spec (p := IsGaugedOperator a X J μ) ⟨T, fun x y => ?_, fun x => ?_⟩
  · rw [← hc, ← hc]
    exact hs x y
  · rw [← hc, hf, hq]
private theorem chainLogWeight_eq_at {a : ℝ} (hN : GaussianNumberViaBorderedDeterminant)
    (hL : 0 < L) (hA : LevelFormsEuclidean L n k) (hC : EdgeFormsEuclidean L n k k)
    (h₀ : VertexFunctionsEuclidean L n k 0) (hk : VertexFunctionsEuclidean L n k k)
    {X : ChainPoint L n k} (hm : ChainLinearMapsAt X)
    (hT0 : ∀ ξ, 0 ≤ fibreHessian a X ξ)
    (hTnull : ∀ ξ : LinearMap.ker (topDeriv X), fibreHessian a X ξ = 0 ↔
      (ξ : LevelForms L n k) ∈ (topVanishingGauges L n k).map (gaugeOrbitMap X))
    (hghost : LinearMap.det (ghostBlockOperator X) ≠ 0)
    {J : LevelForms L n k} {μ : edgeFormSpace L n k k}
    (q : QuadraticForm ℝ (LevelForms L n k)) (hq : ∀ ξ, q ξ = gaugedRightValue a X J μ ξ)
    (hform : ∀ ξ ∈ LinearMap.ker (shiftedGaugeMap X),
      ∃ η : LinearMap.ker (topDeriv X), (η : LevelForms L n k) = _root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X ξ ∧
        fibreHessian a X η = gaugedFormValue a X J μ ξ)
    {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (l : LevelForms L n k →ₗ[ℝ] Y) (hl : IsTransversalSlice X l) :
    levelSaddleDet (gaugedOperator a X J μ) (shiftedGaugeMap X) ≠ 0 ∧
      chainLogWeight a X l = chainFreeEnergy a X J μ + towerLogConstant L n k := by
  classical
  haveI := hA.1
  haveI := hC.1
  haveI := h₀.1
  haveI := hk.1
  set cA := hA.2.choose with hcA
  set cC := hC.2.choose with hcC
  set cG := h₀.2.choose with hcG
  set cGc := hk.2.choose with hcGc
  have iA : IsLevelCore cA := hA.2.choose_spec
  have iC : IsEdgePairingCore cC := hC.2.choose_spec
  have iG : IsVertexPairingCore cG := h₀.2.choose_spec
  have iGc : IsVertexPairingCore cGc := hk.2.choose_spec
  have hb : 0 < ((L : ℝ) ^ (4 * k))⁻¹ := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    positivity
  set b : ℝ := ((L : ℝ) ^ (4 * k))⁻¹ with hbdef
  set D := gaugeOrbitMap X with hD
  set Q := topDeriv X with hQ
  set Q' := shiftedGaugeMap X with hQ'
  set r := restrictToTopLinear L n k with hr
  set rt := extendFromTopLinear L n k with hrt
  set n₀ := chainDriftMap X with hn₀
  set Dc := topCovDiffLinear (levelField X k) with hDc
  set aa := composedCubeAverageLinear X with haa
  set r₂ := iterAverageLinear L n k X.fine with hr₂
  set t₂ := iterAverageRealTranspose L n k X.fine with ht₂
  set p := fineSlotTranspose (L := L) (n := n) (k := k) X.fine with hp
  obtain ⟨t₁, ht₁, haat₁⟩ := hm.mean_transpose
  have hK : topVanishingGauges L n k = LinearMap.ker r := by
    ext x
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      exact Subtype.ext ((hm.restrict_apply x).trans (funext h))
    · intro h y
      have h1 := hm.restrict_apply x
      rw [← hr, h] at h1
      exact (congrFun h1 y).symm
  have hQ'a : ∀ ξ, Q' ξ = Q ξ + Dc (n₀ ξ) := fun ξ => by
    apply Subtype.ext
    rw [hm.shifted_spec ξ]
    show shiftedGaugeValues X ξ = (Q ξ : Edge L n k k → ComplexMatrix2) +
      (Dc (n₀ ξ) : Edge L n k k → ComplexMatrix2)
    rw [hm.topDeriv_spec ξ, hm.topCovDiff_apply, hm.drift_spec ξ]
    rfl
  have hgc : IsGaugeTransform X (LinearMap.id + D ∘ₗ rt ∘ₗ n₀) := fun ξ => by
    have h1 : ((rt (n₀ ξ) : vertexFunctionSpace L n k 0) : Vertex L n k 0 → ComplexMatrix2) =
        gaugeCorrection X ξ := by
      rw [hm.extend_apply, hm.drift_spec ξ]
      rfl
    have h2 := hm.orbit_spec (rt (n₀ ξ))
    rw [h1] at h2
    rw [← h2]
    rfl
  have hgc' : _root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X = LinearMap.id + D ∘ₗ rt ∘ₗ n₀ := by
    have hs : IsGaugeTransform X (_root_.YangMills.Construction.RunningCouplingSlope.gaugeTransform X) :=
      Classical.epsilon_spec (p := IsGaugeTransform X) ⟨_, hgc⟩
    refine LinearMap.ext fun ξ => formValues_injective ?_
    rw [hs ξ, hgc ξ]
  have hop := gaugedOperator_spec hA q hq
  have hpD : p ∘ₗ D = covDiffRealTranspose L n k X.fine ∘ₗ
      covDiffLinear L n k X.fine := LinearMap.ext fun x => by
    show covDiffRealTranspose L n k X.fine (D x).1 = _
    rw [hm.orbit_fst]
    rfl
  have hghost' : ghostBlockOperator X = borderedBlockOperator (p ∘ₗ D) t₂ aa := by
    rw [hpD]
    rfl
  have hgauge : ∀ ξ : LevelForms L n k, (gaugeSliceResidual X.fine ξ.1 : vertexFunctionSpace L n k 0) =
      p ξ - b⁻¹ • t₂ (r₂ (p ξ)) := fun ξ => by
    rw [hbdef, inv_inv]
    rfl
  have key := gaussianNumber_through_cores hN cA cC cG cGc D Dc Q Q' r r₂ aa n₀ p rt t₁ t₂ b
    (fibreHessian a X) (gaugedOperator a X J μ) l
    (topVanishingGauges L n k) hK hm.topDeriv_surjective
    (fun g x => by
      rw [iG, iGc, hm.extend_pairing])
    hm.restrict_extend hm.topDeriv_orbit hb hm.mean_eq hQ'a
    (fun g x => by rw [iG, iGc, ht₁])
    haat₁ hm.mean_extend
    (fun g x => by rw [iG, iGc, hm.iterTranspose_pairing])
    hm.iterAverage_transpose hm.orbit_injective hT0 hTnull (by rwa [← hghost'])
    (fun x y => by rw [iA, iA]; exact hop.1 x y)
    (fun ξ hξ h => by
      obtain ⟨η, hη, hηf⟩ := hform ξ (LinearMap.mem_ker.mpr hξ)
      have e₁ : (⟨_, h⟩ : LinearMap.ker Q) = η := Subtype.ext (by
        rw [hη, hgc']
        rfl)
      rw [iA, hop.2 ξ, e₁, hηf, ← hgauge ξ, iG]
      unfold gaugedRightValue traceFinsumNorm
      rw [Real.sq_sqrt]
      have := cG.re_inner_nonneg (gaugeSliceResidual X.fine ξ.1)
      rw [iG] at this
      simpa using this)
    hl
  have eS : levelSaddleDet (gaugedOperator a X J μ) Q' =
      saddleDetOfCores cA cC (gaugedOperator a X J μ) Q' := by
    unfold levelSaddleDet
    rw [dif_pos ⟨hA, hC⟩]
  have eI : ∀ T, levelGaussianNumber Q T = constrainedGaussianNumberOfCores cA cC Q T := fun T => by
    unfold levelGaussianNumber
    rw [dif_pos ⟨hA, hC⟩]
  have eV : sliceOrbitVolume X l =
      (letI := cG.toNormedAddCommGroup
       letI := InnerProductSpace.ofCore cG.toCore
       absDetOfMap (l ∘ₗ D ∘ₗ (topVanishingGauges L n k).subtype)) := by
    unfold sliceOrbitVolume
    rw [dif_pos h₀]
  obtain ⟨hS, hnum⟩ := key
  have hSne : levelSaddleDet (gaugedOperator a X J μ) Q' ≠ 0 := by rwa [eS]
  refine ⟨hSne, ?_⟩
  have hc : 0 < (b ^ finrank ℝ (vertexFunctionSpace L n k k)) ^ (1 / 2 : ℝ) *
      (b ^ finrank ℝ (vertexFunctionSpace L n k k))⁻¹ *
      (2 * Real.pi) ^ (((finrank ℝ (LevelForms L n k) : ℝ) -
        (finrank ℝ (edgeFormSpace L n k k) : ℝ)) / 2) := by
    have : 0 < 2 * Real.pi := by positivity
    positivity
  unfold chainLogWeight chainFreeEnergy
  rw [eI, eV, hnum, log_mul_rpow_abs _ _ _ hc hS (by rwa [← hghost']), ← hghost', ← eS]
  show _ = _ + Real.log _
  ring
private theorem exists_left_inverse_of_injective {U V : Type} [AddCommGroup U] [Module ℝ U]
    [AddCommGroup V] [Module ℝ V] (f : U →ₗ[ℝ] V) (h : Function.Injective f) :
    ∃ g : V →ₗ[ℝ] U, g ∘ₗ f = LinearMap.id :=
  LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.mpr h)
private theorem exists_equiv_euclideanSpace {U : Type} [AddCommGroup U] [Module ℝ U]
    [FiniteDimensional ℝ U] (K : Submodule ℝ U) :
    ∃ d : ℕ, Nonempty (K ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
  ⟨finrank ℝ K, ⟨LinearEquiv.ofFinrankEq _ _ (by simp)⟩⟩
private theorem exists_transversalSlice (hfin : FiniteDimensional ℝ (vertexFunctionSpace L n k 0))
    {X : ChainPoint L n k}
    (hinj : Function.Injective (gaugeOrbitMap X ∘ₗ (topVanishingGauges L n k).subtype)) :
    ∃ (d : ℕ) (l : LevelForms L n k →ₗ[ℝ] EuclideanSpace ℝ (Fin d)), IsTransversalSlice X l := by
  haveI := hfin
  obtain ⟨g, hg⟩ := exists_left_inverse_of_injective (U := topVanishingGauges L n k)
    (V := LevelForms L n k) (gaugeOrbitMap X ∘ₗ (topVanishingGauges L n k).subtype) hinj
  obtain ⟨d, ⟨e⟩⟩ := exists_equiv_euclideanSpace (U := vertexFunctionSpace L n k 0)
    (topVanishingGauges L n k)
  refine ⟨d, e.toLinearMap ∘ₗ g, ?_⟩
  have h : (e.toLinearMap ∘ₗ g) ∘ₗ gaugeOrbitMap X ∘ₗ (topVanishingGauges L n k).subtype =
      e.toLinearMap := by
    rw [LinearMap.comp_assoc, hg, LinearMap.comp_id]
  unfold IsTransversalSlice
  rw [h]
  exact e.bijective
private theorem analyticAt_matrix_det {ι E : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {A : E → Matrix ι ι ℝ} {x : E}
    (h : ∀ i j, AnalyticAt ℝ (fun w => A w i j) x) : AnalyticAt ℝ (fun w => (A w).det) x := by
  simp only [Matrix.det_apply']
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => h _ _)
section Determinants
variable {A C E : Type} [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A]
  [AddCommGroup C] [Module ℝ C] [FiniteDimensional ℝ C]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem det_saddlePointOperator_eq_blocks {E' F : Type} [NormedAddCommGroup E']
    [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (v : OrthonormalBasis α ℝ E') (w : OrthonormalBasis β ℝ F) (X : E' →ₗ[ℝ] E')
    (M : E' →ₗ[ℝ] F) :
    LinearMap.det (saddlePointOperator X M) =
      (Matrix.fromBlocks (LinearMap.toMatrix v.toBasis v.toBasis X)
        (LinearMap.toMatrix v.toBasis w.toBasis M).transpose
        (LinearMap.toMatrix v.toBasis w.toBasis M) 0).det := by apply _root_.YangMills.Construction.GaussianConstraint.SaddleDeterminant.det_saddlePointOperator_eq_det_fromBlocks <;> assumption
private theorem analyticAt_saddleDetOfCores (cA : InnerProductSpace.Core ℝ A)
    (cC : InnerProductSpace.Core ℝ C) (Tw : E → A →ₗ[ℝ] A) (Mw : E → A →ₗ[ℝ] C) (R : E → A → ℝ)
    (x : E)
    (hs : ∀ᶠ w in 𝓝 x, (∀ ξ ξ', cA.inner ξ (Tw w ξ') = cA.inner (Tw w ξ) ξ') ∧
      ∀ ξ, cA.inner ξ (Tw w ξ) = R w ξ)
    (hR : ∀ ξ, AnalyticAt ℝ (fun w => R w ξ) x)
    (hM : ∀ ξ c, AnalyticAt ℝ (fun w => cC.inner c (Mw w ξ)) x) :
    AnalyticAt ℝ (fun w => saddleDetOfCores cA cC (Tw w) (Mw w)) x := by
  classical
  let := cA.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cA.toCore
  let := cC.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cC.toCore
  let v := stdOrthonormalBasis ℝ A
  let u := stdOrthonormalBasis ℝ C
  let Em : E → Matrix _ _ ℝ := fun w => Matrix.of fun i j =>
    (R w (v i + v j) - R w (v i) - R w (v j)) / 2
  let Mm : E → Matrix _ _ ℝ := fun w => Matrix.of fun f i => cC.inner (u f) (Mw w (v i))
  have hP : AnalyticAt ℝ (fun w =>
      (Matrix.fromBlocks (Em w) (Mm w).transpose (Mm w) 0).det) x := by
    refine analyticAt_matrix_det fun i j => ?_
    rcases i with i | i <;> rcases j with j | j
    · exact (((hR _).sub (hR _)).sub (hR _)).div_const
    · exact hM _ _
    · exact hM _ _
    · exact analyticAt_const
  refine hP.congr ?_
  filter_upwards [hs] with w hw
  have h₁ : LinearMap.toMatrix v.toBasis v.toBasis (Tw w) = Em w := by
    ext i j
    have hpol := hw.2 (v i + v j)
    have hi := hw.2 (v i)
    have hj := hw.2 (v j)
    have hsym := hw.1 (v j) (v i)
    have hcomm : cA.inner (Tw w (v j)) (v i) = cA.inner (v i) (Tw w (v j)) := by
      have := cA.conj_inner_symm (v i) (Tw w (v j))
      simpa using this
    have hadd : cA.inner (v i + v j) (Tw w (v i + v j)) =
        cA.inner (v i) (Tw w (v i)) + cA.inner (v j) (Tw w (v j)) +
          (cA.inner (v i) (Tw w (v j)) + cA.inner (v j) (Tw w (v i))) := by
      have e₁ : ∀ x y z : A, cA.inner x (y + z) = cA.inner x y + cA.inner x z := fun x y z =>
        inner_add_right (𝕜 := ℝ) x y z
      rw [map_add, e₁, cA.add_left, cA.add_left]
      ring
    simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, Em,
      Matrix.of_apply]
    show cA.inner (v i) (Tw w (v j)) = _
    rw [← hpol, ← hi, ← hj, hadd]
    rw [hsym, hcomm]
    ring
  have h₂ : LinearMap.toMatrix v.toBasis u.toBasis (Mw w) = Mm w := by
    ext f i
    simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, Mm,
      Matrix.of_apply]
  show _ = LinearMap.det (saddlePointOperator (Tw w) (Mw w))
  rw [det_saddlePointOperator_eq_blocks v u, h₁, h₂]
private theorem analyticAt_det_prod_of_entries (cA : InnerProductSpace.Core ℝ A)
    (cC : InnerProductSpace.Core ℝ C) (f : E → (A × C) →ₗ[ℝ] A × C) (x : E)
    (hf : ∀ x' y : A × C, AnalyticAt ℝ (fun w =>
      cA.inner x'.1 (f w y).1 + cC.inner x'.2 (f w y).2) x) :
    AnalyticAt ℝ (fun w => LinearMap.det (f w)) x := by
  classical
  let := cA.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cA.toCore
  let := cC.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cC.toCore
  let v := stdOrthonormalBasis ℝ A
  let u := stdOrthonormalBasis ℝ C
  let b := v.toBasis.prod u.toBasis
  have h : (fun w => LinearMap.det (f w)) = fun w => (LinearMap.toMatrix b b (f w)).det :=
    funext fun w => (LinearMap.det_toMatrix b _).symm
  rw [h]
  refine analyticAt_matrix_det fun i j => ?_
  rcases i with i | i
  · have h₂ := hf (v i, 0) (b j)
    refine h₂.congr (Eventually.of_forall fun w => ?_)
    have h₃ : cC.inner (0 : C) ((f w (b j)).2) = 0 := inner_zero_left (𝕜 := ℝ) _
    simp only [h₃, add_zero, LinearMap.toMatrix_apply]
    simp [b, Module.Basis.prod_repr_inl, OrthonormalBasis.repr_apply_apply]
  · have h₂ := hf (0, u i) (b j)
    refine h₂.congr (Eventually.of_forall fun w => ?_)
    have h₃ : cA.inner (0 : A) ((f w (b j)).1) = 0 := inner_zero_left (𝕜 := ℝ) _
    simp only [h₃, zero_add, LinearMap.toMatrix_apply]
    simp [b, Module.Basis.prod_repr_inr, OrthonormalBasis.repr_apply_apply]
abbrev _root_.YangMills.SharedProofs.p93035 := @analyticAt_det_prod_of_entries
private theorem symm_operator_eq_of_forms (cA : InnerProductSpace.Core ℝ A) (T T' : A →ₗ[ℝ] A)
    (hT : ∀ ξ ξ', cA.inner ξ (T ξ') = cA.inner (T ξ) ξ')
    (hT' : ∀ ξ ξ', cA.inner ξ (T' ξ') = cA.inner (T' ξ) ξ')
    (h : ∀ ξ, cA.inner ξ (T ξ) = cA.inner ξ (T' ξ)) : T = T' := by
  let := cA.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cA.toCore
  have hs : ∀ (S : A →ₗ[ℝ] A), (∀ ξ ξ', cA.inner ξ (S ξ') = cA.inner (S ξ) ξ') →
      ∀ x y, inner ℝ (x + y) (S (x + y)) =
        inner ℝ x (S x) + inner ℝ y (S y) + 2 * inner ℝ x (S y) := fun S hS x y => by
    have h₁ : inner ℝ y (S x) = inner ℝ x (S y) := by
      have h₂ : inner ℝ y (S x) = inner ℝ (S y) x := hS y x
      rw [h₂, real_inner_comm]
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, h₁]
    ring
  refine LinearMap.ext fun y => ext_inner_left ℝ fun x => ?_
  have h₁ := hs T hT x y
  have h₂ := hs T' hT' x y
  have h₃ : inner ℝ (x + y) (T (x + y)) = inner ℝ (x + y) (T' (x + y)) := h (x + y)
  have h₄ : inner ℝ x (T x) = inner ℝ x (T' x) := h x
  have h₅ : inner ℝ y (T y) = inner ℝ y (T' y) := h y
  linarith
private theorem saddleDetOfCores_conj (cA : InnerProductSpace.Core ℝ A)
    (cC : InnerProductSpace.Core ℝ C)
    (T T' : A →ₗ[ℝ] A) (M M' : A →ₗ[ℝ] C) (Aq : A ≃ₗ[ℝ] A) (Fq : C ≃ₗ[ℝ] C)
    (hA : ∀ ξ ξ', cA.inner (Aq ξ) (Aq ξ') = cA.inner ξ ξ')
    (hF : ∀ c c', cC.inner (Fq c) (Fq c') = cC.inner c c')
    (hT : ∀ ξ, T' (Aq ξ) = Aq (T ξ)) (hM : ∀ ξ, M' (Aq ξ) = Fq (M ξ)) :
    saddleDetOfCores cA cC T' M' = saddleDetOfCores cA cC T M := by
  let := cA.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cA.toCore
  let := cC.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cC.toCore
  show LinearMap.det (saddlePointOperator T' M') = LinearMap.det (saddlePointOperator T M)
  have hadj : ∀ c, LinearMap.adjoint M' (Fq c) = Aq (LinearMap.adjoint M c) := fun c => by
    refine ext_inner_right ℝ fun y => ?_
    obtain ⟨ξ, rfl⟩ := Aq.surjective y
    rw [LinearMap.adjoint_inner_left, hM]
    have h₁ : inner ℝ (Fq c) (Fq (M ξ)) = inner ℝ c (M ξ) := hF _ _
    have h₂ : inner ℝ (Aq (LinearMap.adjoint M c)) (Aq ξ) =
      inner ℝ (LinearMap.adjoint M c) ξ := hA _ _
    rw [h₁, h₂, LinearMap.adjoint_inner_left]
  let e : (A × C) ≃ₗ[ℝ] A × C := Aq.prodCongr Fq
  have hconj : saddlePointOperator T' M' =
      (e : (A × C) →ₗ[ℝ] A × C) ∘ₗ saddlePointOperator T M ∘ₗ (e.symm : (A × C) →ₗ[ℝ] A × C) := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨z, rfl⟩ := e.surjective y
    rcases z with ⟨ξ, c⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    refine Prod.ext ?_ ?_
    · show T' (Aq ξ) + LinearMap.adjoint M' (Fq c) = Aq (T ξ + LinearMap.adjoint M c)
      rw [hT, hadj, map_add]
    · exact hM ξ
  rw [hconj, LinearMap.det_conj]
private theorem symm_operator_conj (cA : InnerProductSpace.Core ℝ A) (T T' : A →ₗ[ℝ] A)
    (Aq : A ≃ₗ[ℝ] A) (hA : ∀ ξ ξ', cA.inner (Aq ξ) (Aq ξ') = cA.inner ξ ξ')
    (hT : ∀ ξ ξ', cA.inner ξ (T ξ') = cA.inner (T ξ) ξ')
    (hT' : ∀ ξ ξ', cA.inner ξ (T' ξ') = cA.inner (T' ξ) ξ')
    (R R' : A → ℝ) (hTf : ∀ ξ, cA.inner ξ (T ξ) = R ξ) (hTf' : ∀ ξ, cA.inner ξ (T' ξ) = R' ξ)
    (hR : ∀ ξ, R' (Aq ξ) = R ξ) (ξ : A) : T' (Aq ξ) = Aq (T ξ) := by
  have h : T' = (Aq : A →ₗ[ℝ] A) ∘ₗ T ∘ₗ (Aq.symm : A →ₗ[ℝ] A) := by
    refine symm_operator_eq_of_forms cA _ _ hT' (fun x y => ?_) fun x => ?_
    · obtain ⟨x', rfl⟩ := Aq.surjective x
      obtain ⟨y', rfl⟩ := Aq.surjective y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      rw [hA, hA, hT]
    · obtain ⟨x', rfl⟩ := Aq.surjective x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      rw [hTf', hR, hA, hTf]
  rw [h]
  simp
private theorem det_eq_of_intertwine {V : Type} [AddCommGroup V] [Module ℝ V] (f f' : V →ₗ[ℝ] V)
    (e : V ≃ₗ[ℝ] V) (h : ∀ y, f' (e y) = e (f y)) : LinearMap.det f' = LinearMap.det f := by
  have hc : f' = (e : V →ₗ[ℝ] V) ∘ₗ f ∘ₗ (e.symm : V →ₗ[ℝ] V) := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨z, rfl⟩ := e.surjective y
    simp [h]
  rw [hc, LinearMap.det_conj]
end Determinants
private theorem levelSaddleDet_eq [FiniteDimensional ℝ (LevelForms L n k)]
    [FiniteDimensional ℝ (edgeFormSpace L n k k)] (hA : LevelFormsEuclidean L n k)
    (hC : EdgeFormsEuclidean L n k k) (T : LevelForms L n k →ₗ[ℝ] LevelForms L n k)
    (M : LevelForms L n k →ₗ[ℝ] edgeFormSpace L n k k) :
    levelSaddleDet T M = saddleDetOfCores hA.2.choose hC.2.choose T M := by
  unfold levelSaddleDet
  rw [dif_pos ⟨hA, hC⟩]
private theorem expMove_zero_unitPoint :
    expMove (0 : LevelForms L n k) (unitPoint L n k) = unitPoint L n k := by apply _root_.YangMills.SharedProofs.p5970 <;> assumption
private theorem edgeFormPairing_zero_left {j : ℕ} (B : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing (0 : Edge L n k j → ComplexMatrix2) B = 0 := by apply _root_.YangMills.Construction.Tower.CriticalSecondDeriv.edgeFormPairing_zero <;> assumption
private theorem isTopMultiplier_zero :
    IsTopMultiplier (unitPoint L n k) 0 (0 : edgeFormSpace L n k k) := by
  intro ξ
  have h₂ : levelPairing (formValues (0 : LevelForms L n k)) (formValues ξ) = 0 := by
    unfold levelPairing formValues
    have h₃ : ∀ i : Fin k, edgeFormPairing (((0 : LevelForms L n k).2 i : edgeFormSpace L n k (i + 1)) :
        Edge L n k (i + 1) → ComplexMatrix2) (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) = 0 :=
      fun i => edgeFormPairing_zero_left _
    have h₄ : edgeFormPairing (((0 : LevelForms L n k).1 : edgeFormSpace L n k 0) :
        Edge L n k 0 → ComplexMatrix2) (ξ.1 : Edge L n k 0 → ComplexMatrix2) = 0 :=
      edgeFormPairing_zero_left _
    simp only [h₃, h₄, Complex.zero_re, Finset.sum_const_zero, add_zero]
  rw [h₂]
  have h₅ : edgeFormPairing (((0 : edgeFormSpace L n k k) : edgeFormSpace L n k k) :
      Edge L n k k → ComplexMatrix2)
      (topDeriv (unitPoint L n k) ξ : Edge L n k k → ComplexMatrix2) = 0 :=
    edgeFormPairing_zero_left _
  rw [h₅, Complex.zero_re]
private theorem log_abs_eq_half_log_sq (x : ℝ) : Real.log |x| = (1 / 2) * Real.log (x ^ 2) := by
  rw [Real.log_pow, Real.log_abs]
  push_cast
  ring
private theorem analyticAt_log_abs_of_ne {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : AnalyticAt ℝ f x) (h : f x ≠ 0) :
    AnalyticAt ℝ (fun w => Real.log |f w|) x := by
  simp only [log_abs_eq_half_log_sq]
  have hp : 0 < f x ^ 2 := by positivity
  have h2 : AnalyticAt ℝ (fun w => f w ^ 2) x := hf.pow 2
  exact analyticAt_const.mul
    (AnalyticAt.comp (g := Real.log) (f := fun w => f w ^ 2) (analyticAt_log hp) h2)
theorem holds (hOne : ChainLogIsGaussianNumber) (hForm : FibreHessianAfterGaugeChange)
    (hN : GaussianNumberViaBorderedDeterminant)
    (hMaps : ChainMapsAtMinimizers) (hFib : FibreHessianAtMinimizer)
    (hGrad : GradientsAtMinimizer) (hGF : GhostInvertibleAndQuadraticRightSide)
    (hFlat : UnitPointIsMinimizer) (hGrad0 : GradientAtUnitPoint)
    (hEnt : ChainFunctionEntriesAnalytic)
    (hCov : ChainFunctionGaugeCovariance)
    (hSp : FiniteSideFormSpaces)
    (hSite : FormOnAFibre.VertexFunctionsAreEuclidean.Statement) :
    ChainFreeEnergyAnalytic.Claim := by
  intro a ha L hL k n hk hn
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hA : LevelFormsEuclidean L n k := levelFormsEuclidean_of hSp hL hn
  have hC : EdgeFormsEuclidean L n k k := by
    obtain ⟨-, f, -, c, h⟩ := hSp L n k k hL hn le_rfl
    exact ⟨f, c, fun B B' => by rw [h B B', Complex.ofReal_re]⟩
  have h₀ : VertexFunctionsEuclidean L n k 0 := hSite L n k 0 hL hn (Nat.zero_le k)
  have hk' : VertexFunctionsEuclidean L n k k := hSite L n k k hL hn le_rfl
  obtain ⟨hread, hleast⟩ := hFlat a ha L hL k n hk hn
  have hgrad := hGrad0 a ha L hL k n hk hn
  have hM' := hMaps a ha L hL k n hk hn
  have hFi' := hFib a ha L hL k n hk hn
  have hGF' := hGF a ha L hL k n hk hn
  have hFo' := hForm a ha L hL k n hk hn
  have fM := hM'.self_of_nhds _ hread _ hleast
  have fF := hFi'.self_of_nhds _ hread _ hleast
  obtain ⟨fG, fQ⟩ := hGF'.self_of_nhds _ hread _ hleast
  obtain ⟨q₀, hq₀⟩ := fQ 0 0
  have fO := hFo'.self_of_nhds _ hread _ hleast 0 0 hgrad isTopMultiplier_zero
  obtain ⟨d₀, l₀, hl₀⟩ := exists_transversalSlice (k := k) h₀.1 fM.orbit_injective
  have nFlat := chainLogWeight_eq_at hN hL0 hA hC h₀ hk' fM fF.1 fF.2 fG q₀ hq₀ fO l₀ hl₀
  refine ⟨fun N e => ⟨?_, ?_⟩, fun ρ hρ hρ1 => ?_⟩
  · obtain ⟨hq, hR, hMc, hGh, hLn⟩ := hEnt a ha L hL k n hk hn N e
    haveI := hA.1
    haveI := hC.1
    haveI := h₀.1
    haveI := hk'.1
    have iA : IsLevelCore hA.2.choose := hA.2.choose_spec
    have iC : IsEdgePairingCore hC.2.choose := hC.2.choose_spec
    have iG : IsVertexPairingCore h₀.2.choose := h₀.2.choose_spec
    have iGc : IsVertexPairingCore hk'.2.choose := hk'.2.choose_spec
    have hS : AnalyticAt ℝ (fun w => levelSaddleDet
        (gaugedOperator a (expMove (e w).1 (unitPoint L n k)) (e w).2.1 (e w).2.2)
        (shiftedGaugeMap (expMove (e w).1 (unitPoint L n k)))) 0 := by
      have heq : (fun w => levelSaddleDet
          (gaugedOperator a (expMove (e w).1 (unitPoint L n k)) (e w).2.1 (e w).2.2)
          (shiftedGaugeMap (expMove (e w).1 (unitPoint L n k)))) = fun w =>
          saddleDetOfCores hA.2.choose hC.2.choose
            (gaugedOperator a (expMove (e w).1 (unitPoint L n k)) (e w).2.1 (e w).2.2)
            (shiftedGaugeMap (expMove (e w).1 (unitPoint L n k))) :=
        funext fun w => levelSaddleDet_eq hA hC _ _
      rw [heq]
      refine analyticAt_saddleDetOfCores _ _ _ _
        (fun w ξ => gaugedRightValue a (expMove (e w).1 (unitPoint L n k)) (e w).2.1 (e w).2.2 ξ) 0
        ?_ hR ?_
      · filter_upwards [hq] with w hw
        obtain ⟨q, hqw⟩ := hw
        have hop := gaugedOperator_spec hA q hqw
        exact ⟨fun ξ ξ' => by rw [iA, iA]; exact hop.1 ξ ξ', fun ξ => by rw [iA]; exact hop.2 ξ⟩
      · intro ξ c
        refine (hMc ξ c).congr (Eventually.of_forall fun w => ?_)
        exact (iC c _).symm
    have hG : AnalyticAt ℝ (fun w =>
        LinearMap.det (ghostBlockOperator (expMove (e w).1 (unitPoint L n k)))) 0 := by
      refine analyticAt_det_prod_of_entries h₀.2.choose hk'.2.choose _ 0 fun x y => ?_
      refine (hGh x y).congr (Eventually.of_forall fun w => ?_)
      exact congrArg₂ (· + ·) (iG _ _).symm (iGc _ _).symm
    have he0 : e 0 = 0 := map_zero e
    have hS0 : levelSaddleDet
        (gaugedOperator a (expMove (e 0).1 (unitPoint L n k)) (e 0).2.1 (e 0).2.2)
        (shiftedGaugeMap (expMove (e 0).1 (unitPoint L n k))) ≠ 0 := by
      simp only [he0, Prod.fst_zero, Prod.snd_zero, expMove_zero_unitPoint]
      exact nFlat.1
    have hG0 : LinearMap.det (ghostBlockOperator (expMove (e 0).1 (unitPoint L n k))) ≠ 0 := by
      simp only [he0, Prod.fst_zero, expMove_zero_unitPoint]
      exact fG
    unfold tripleFreeEnergy chainFreeEnergy
    exact ((analyticAt_const.mul (analyticAt_log_abs_of_ne hS hS0)).add
      (analyticAt_const.mul hLn)).add (analyticAt_log_abs_of_ne hG hG0)
  · obtain ⟨δ, hδ, hcov⟩ := hCov a ha L hL k n hk hn N e
    obtain ⟨hq, -⟩ := hEnt a ha L hL k n hk hn N e
    refine ⟨δ, hδ, ?_⟩
    filter_upwards [hcov, hq] with w hw hqw v hv hvn J' μ' hJ hμ
    obtain ⟨hlog, ⟨q', hq'⟩, Aq, Fq, G₀, Gk, -, -, -, -, hAi, hFi, hRf, hQc, hgh⟩ :=
      hw v hv hvn J' μ' hJ hμ
    obtain ⟨q, hq₁⟩ := hqw
    haveI := hA.1
    haveI := hC.1
    have iA : IsLevelCore hA.2.choose := hA.2.choose_spec
    have iC : IsEdgePairingCore hC.2.choose := hC.2.choose_spec
    have hop := gaugedOperator_spec hA q hq₁
    have hop' := gaugedOperator_spec hA q' hq'
    have hAc : ∀ ξ ξ', hA.2.choose.inner (Aq ξ) (Aq ξ') = hA.2.choose.inner ξ ξ' := fun ξ ξ' => by
      rw [iA, iA]
      exact hAi ξ ξ'
    have hFc : ∀ c c', hC.2.choose.inner (Fq c) (Fq c') = hC.2.choose.inner c c' := fun c c' => by
      rw [iC, iC]
      exact hFi c c'
    have hT := symm_operator_conj hA.2.choose _ _ Aq hAc
      (fun ξ ξ' => by rw [iA, iA]; exact hop.1 ξ ξ')
      (fun ξ ξ' => by rw [iA, iA]; exact hop'.1 ξ ξ')
      _ _ (fun ξ => by rw [iA]; exact hop.2 ξ) (fun ξ => by rw [iA]; exact hop'.2 ξ) hRf
    have hsad := saddleDetOfCores_conj hA.2.choose hC.2.choose _ _ _ _ Aq Fq hAc hFc hT hQc
    have hdet := det_eq_of_intertwine (ghostBlockOperator (expMove (e w).1 (unitPoint L n k)))
      (ghostBlockOperator (gaugeTransformPoint v (expMove (e w).1 (unitPoint L n k))))
      (G₀.prodCongr Gk) fun y => hgh y
    unfold tripleFreeEnergy chainFreeEnergy
    rw [hlog, hdet, levelSaddleDet_eq hA hC, levelSaddleDet_eq hA hC, hsad]
  · filter_upwards [hOne a ha L hL k n hk hn ρ hρ hρ1, hFo', hM', hFi',
      hGrad a ha L hL k n hk hn, hGF'] with V h1 h2 h3 h4 h5 h6 W hW X hX
    obtain ⟨J, μ, g1, g2, g3⟩ := h5 W hW X hX
    refine ⟨J, μ, g1, g2, g3, ?_⟩
    have xM := h3 W hW X hX
    have xF := h4 W hW X hX
    obtain ⟨xG, xQ⟩ := h6 W hW X hX
    obtain ⟨q, hq⟩ := xQ J μ
    obtain ⟨d, l, hl⟩ := exists_transversalSlice (k := k) h₀.1 xM.orbit_injective
    have nX := chainLogWeight_eq_at hN hL0 hA hC h₀ hk' xM xF.1 xF.2 xG q hq
      (h2 W hW X hX J μ g1 g2) l hl
    rw [(h1 W hW).2 X hX _ _ l l₀ hl hl₀, nX.2, nFlat.2]
    ring
end YangMills.Construction.RunningCouplingSlope.ChainFreeEnergyAnalytic
end
