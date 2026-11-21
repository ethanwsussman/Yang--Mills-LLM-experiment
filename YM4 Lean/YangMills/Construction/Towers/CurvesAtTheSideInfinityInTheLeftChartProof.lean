import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.Matrices.FiniteMatrixProducts
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfigurationProof
import YangMills.Construction.Towers.CurvesAtTheSideInfinityInTheLeftChart
import YangMills.Construction.Towers.MapOfAWritingNearThePoint
import YangMills.Construction.Towers.OneValueForEveryWriting
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower.FullSpaceCurveDifferentials
section Submanifold
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem differentiableAt_of_contDiffOn_mem_nhds {E' : Type} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {g : E → E'} {s : Set E} {x : E} (h : ContDiffOn ℝ ∞ g s)
    (hs : s ∈ 𝓝 x) : DifferentiableAt ℝ g x :=
  (h.contDiffAt hs).differentiableAt (by simp)
def straighteningChart {M : Set E} {l l' : ℕ}
    (q : OpenPartialHomeomorph E ((Fin l → ℝ) × (Fin l' → ℝ)))
    (hq : ContDiffOn ℝ ∞ q q.source) (hq' : ContDiffOn ℝ ∞ q.symm q.target)
    (hM : q '' (q.source ∩ M) = q.target ∩ {z | z.2 = 0}) : EmbeddedSubmanifold.Chart M where
  dim := l
  source := {u | (u, (0 : Fin l' → ℝ)) ∈ q.target}
  param := fun u => q.symm (u, 0)
  isOpen_source := q.open_target.preimage (continuous_id.prodMk continuous_const)
  contDiffOn_param :=
    hq'.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun _ h => h
  injective_fderiv_param := by
    intro u hu
    have hopen : IsOpen {u : Fin l → ℝ | (u, (0 : Fin l' → ℝ)) ∈ q.target} :=
      q.open_target.preimage (continuous_id.prodMk continuous_const)
    have hsmooth : ContDiffOn ℝ ∞ (fun u : Fin l → ℝ => q.symm (u, (0 : Fin l' → ℝ)))
        {u | (u, (0 : Fin l' → ℝ)) ∈ q.target} :=
      hq'.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun _ h => h
    have hdiff : DifferentiableAt ℝ (fun u : Fin l → ℝ => q.symm (u, (0 : Fin l' → ℝ))) u :=
      differentiableAt_of_contDiffOn_mem_nhds hsmooth (hopen.mem_nhds hu)
    have hsrc : q.symm (u, (0 : Fin l' → ℝ)) ∈ q.source := q.map_target hu
    have hg : DifferentiableAt ℝ (fun x => (q x).1) (q.symm (u, (0 : Fin l' → ℝ))) :=
      (differentiableAt_of_contDiffOn_mem_nhds hq (q.open_source.mem_nhds hsrc)).fst
    have hcomp := hg.hasFDerivAt.comp u hdiff.hasFDerivAt
    have hid : HasFDerivAt (fun u : Fin l → ℝ => u) (ContinuousLinearMap.id ℝ _) u :=
      hasFDerivAt_id u
    have heq : ((fun x => (q x).1) ∘ fun u : Fin l → ℝ => q.symm (u, (0 : Fin l' → ℝ))) =ᶠ[𝓝 u]
        fun u => u := by
      filter_upwards [hopen.mem_nhds hu] with u' hu'
      have : q (q.symm (u', (0 : Fin l' → ℝ))) = (u', 0) := q.right_inv hu'
      simp [this]
    have huniq := (hcomp.congr_of_eventuallyEq heq.symm).unique hid
    intro x y hxy
    have := congrArg (fun T : (Fin l → ℝ) →L[ℝ] (Fin l → ℝ) => T x) huniq
    have h2 := congrArg (fun T : (Fin l → ℝ) →L[ℝ] (Fin l → ℝ) => T y) huniq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this h2
    rw [← this, ← h2, hxy]
  injOn_param := by
    intro u hu u' hu' h
    have h1 : q (q.symm (u, (0 : Fin l' → ℝ))) = (u, 0) := q.right_inv hu
    have h2 : q (q.symm (u', (0 : Fin l' → ℝ))) = (u', 0) := q.right_inv hu'
    have h3 : q.symm (u, (0 : Fin l' → ℝ)) = q.symm (u', 0) := h
    rw [h3, h2] at h1
    exact (congrArg Prod.fst h1).symm
  isRelativelyOpen_image := by
    intro W hWd hW
    refine ⟨q.source ∩ q ⁻¹' (W ×ˢ univ), q.isOpen_inter_preimage (hW.prod isOpen_univ), ?_⟩
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hut : (u, (0 : Fin l' → ℝ)) ∈ q.target := hWd hu
      have hr : q (q.symm (u, (0 : Fin l' → ℝ))) = (u, 0) := q.right_inv hut
      refine ⟨⟨q.map_target hut, ?_⟩, ?_⟩
      · change q (q.symm (u, (0 : Fin l' → ℝ))) ∈ W ×ˢ univ
        rw [hr]
        exact ⟨hu, mem_univ _⟩
      · have hm : ((u, (0 : Fin l' → ℝ)) : (Fin l → ℝ) × (Fin l' → ℝ)) ∈
            q '' (q.source ∩ M) := by
          rw [hM]
          exact ⟨hut, rfl⟩
        obtain ⟨y, ⟨hy, hyM⟩, hqy⟩ := hm
        have : q.symm (u, (0 : Fin l' → ℝ)) = y := by
          rw [← hqy]
          exact q.left_inv hy
        change q.symm (u, (0 : Fin l' → ℝ)) ∈ M
        rw [this]
        exact hyM
    · rintro ⟨⟨hs, hW'⟩, hxM⟩
      have hm : q x ∈ q.target ∩ {z | z.2 = 0} := by
        rw [← hM]
        exact ⟨x, ⟨hs, hxM⟩, rfl⟩
      have hz : (q x).2 = 0 := hm.2
      refine ⟨(q x).1, hW'.1, ?_⟩
      have : ((q x).1, (0 : Fin l' → ℝ)) = q x := by
        rw [← hz]
      change q.symm ((q x).1, (0 : Fin l' → ℝ)) = x
      rw [this]
      exact q.left_inv hs
theorem exists_hasDerivAt_comp_curve {M O : Set E} (hM : Submanifolds.IsSmoothSubmanifold M)
    {f : E → F} (hf : EmbeddedSubmanifold.DifferentiableOnOpen M O f) {p : E} (hp : p ∈ O)
    (hpM : p ∈ M) (v : E) :
    ∃ d : F, ∀ w : ℝ → E, (∀ᶠ t in 𝓝 (0 : ℝ), w t ∈ M) → w 0 = p → HasDerivAt w v 0 →
      HasDerivAt (fun t => f (w t)) d 0 := by
  obtain ⟨l, l', q, hpq, hq, hq', hqM⟩ := hM p hpM
  let c : EmbeddedSubmanifold.Chart M := straighteningChart q hq hq' hqM
  have hzero : ∀ x ∈ q.source, x ∈ M → (q x).2 = 0 := by
    intro x hx hxM
    have hm : q x ∈ q.target ∩ {z | z.2 = 0} := by
      rw [← hqM]
      exact ⟨x, ⟨hx, hxM⟩, rfl⟩
    exact hm.2
  have hback : ∀ x ∈ q.source, x ∈ M → q.symm ((q x).1, (0 : Fin l' → ℝ)) = x := by
    intro x hx hxM
    have : ((q x).1, (0 : Fin l' → ℝ)) = q x := by
      rw [← hzero x hx hxM]
    rw [this]
    exact q.left_inv hx
  let u₀ : Fin l → ℝ := (q p).1
  have hu₀ : u₀ ∈ c.source := by
    change (u₀, (0 : Fin l' → ℝ)) ∈ q.target
    have : (u₀, (0 : Fin l' → ℝ)) = q p := by
      rw [← hzero p hpq hpM]
    rw [this]
    exact q.map_source hpq
  have hpar : c.param u₀ = p := hback p hpq hpM
  have hinM : ∀ u ∈ c.source, c.param u ∈ M := by
    intro u hu
    have hm : ((u, (0 : Fin l' → ℝ)) : (Fin l → ℝ) × (Fin l' → ℝ)) ∈ q '' (q.source ∩ M) := by
      rw [hqM]
      exact ⟨hu, rfl⟩
    obtain ⟨y, ⟨hy, hyM⟩, hqy⟩ := hm
    have : q.symm (u, (0 : Fin l' → ℝ)) = y := by
      rw [← hqy]
      exact q.left_inv hy
    change q.symm (u, (0 : Fin l' → ℝ)) ∈ M
    rw [this]
    exact hyM
  have hnh : c.coords O ∈ 𝓝 u₀ := by
    obtain ⟨O', hO', hOeq⟩ := hf.1
    have hcont : ContinuousAt c.param u₀ :=
      (c.contDiffOn_param.contDiffAt (c.isOpen_source.mem_nhds hu₀)).continuousAt
    have hpO' : c.param u₀ ∈ O' := by
      rw [hpar]
      rw [hOeq] at hp
      exact hp.1
    filter_upwards [hcont.preimage_mem_nhds (hO'.mem_nhds hpO'), c.isOpen_source.mem_nhds hu₀]
      with u h1 h2
    refine ⟨h2, ?_⟩
    change c.param u ∈ O
    rw [hOeq]
    exact ⟨h1, hinM u h2⟩
  have hread : DifferentiableAt ℝ (c.pullback f) u₀ := (hf.2 c).differentiableAt hnh
  have hg : DifferentiableAt ℝ (fun x => (q x).1) p :=
    (differentiableAt_of_contDiffOn_mem_nhds hq (q.open_source.mem_nhds hpq)).fst
  refine ⟨fderiv ℝ (c.pullback f) u₀ (fderiv ℝ (fun x => (q x).1) p v), fun w hw h0 hd => ?_⟩
  have hu : HasDerivAt (fun t => (q (w t)).1) (fderiv ℝ (fun x => (q x).1) p v) 0 := by
    have h1 : HasFDerivAt (fun x => (q x).1) (fderiv ℝ (fun x => (q x).1) p) (w 0) := by
      rw [h0]
      exact hg.hasFDerivAt
    exact h1.comp_hasDerivAt 0 hd
  have hcomp : HasDerivAt (fun t => c.pullback f (q (w t)).1)
      (fderiv ℝ (c.pullback f) u₀ (fderiv ℝ (fun x => (q x).1) p v)) 0 := by
    have h1 : HasFDerivAt (c.pullback f) (fderiv ℝ (c.pullback f) u₀) (q (w 0)).1 := by
      rw [h0]
      exact hread.hasFDerivAt
    exact h1.comp_hasDerivAt 0 hu
  refine hcomp.congr_of_eventuallyEq ?_
  have hsrc : ∀ᶠ t in 𝓝 (0 : ℝ), w t ∈ q.source := by
    have h1 : ContinuousAt w 0 := hd.continuousAt
    refine h1.preimage_mem_nhds ?_
    rw [h0]
    exact q.open_source.mem_nhds hpq
  filter_upwards [hw, hsrc] with t h1 h2
  change f (w t) = f (q.symm ((q (w t)).1, 0))
  rw [hback _ h2 h1]
end Submanifold
section Holomorphic
open GroupLieProduct
theorem exists_clm_tupleOfCoords_inverse {τ : Type} [Fintype τ]
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (ν : τ ≃ Fin (Fintype.card τ)) :
    ∃ C : (τ → ComplexMatrix2) →L[ℂ] Coordinates.ComplexCoordinates (Fintype.card τ * 3),
      ∀ Z : τ → ComplexMatrix2, (∀ i, Z i ∈ ComplexMatrix2.traceless) →
        tupleOfCoords β ν (C Z) = Z := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (ComplexMatrix2.traceless.subtype)
    (Submodule.ker_subtype _)
  let Cl : (τ → ComplexMatrix2) →ₗ[ℂ] Coordinates.ComplexCoordinates (Fintype.card τ * 3) :=
    LinearMap.pi fun k => (β.coord (finProdFinEquiv.symm k).2) ∘ₗ g ∘ₗ
      LinearMap.proj (ν.symm (finProdFinEquiv.symm k).1)
  refine ⟨LinearMap.toContinuousLinearMap Cl, fun Z hZ => ?_⟩
  funext i
  have h := congrArg (Subtype.val : ComplexMatrix2.traceless → ComplexMatrix2)
    (β.sum_repr ⟨Z i, hZ i⟩)
  rw [Submodule.coe_sum] at h
  have hk : ∀ c, Cl Z (finProdFinEquiv (ν i, c)) = β.repr ⟨Z i, hZ i⟩ c := by
    intro c
    have e : finProdFinEquiv.symm (finProdFinEquiv (ν i, c)) = (ν i, c) :=
      Equiv.symm_apply_apply _ _
    change β.coord (finProdFinEquiv.symm (finProdFinEquiv (ν i, c))).2
      (g (Z (ν.symm (finProdFinEquiv.symm (finProdFinEquiv (ν i, c))).1))) = _
    rw [e]
    simp only [Equiv.symm_apply_apply]
    have hgi : g (Z i) = ⟨Z i, hZ i⟩ := LinearMap.congr_fun hg ⟨Z i, hZ i⟩
    rw [hgi]
    rfl
  calc tupleOfCoords β ν (LinearMap.toContinuousLinearMap Cl Z) i
      = ∑ c, Cl Z (finProdFinEquiv (ν i, c)) • (β c : ComplexMatrix2) := rfl
    _ = ∑ c, β.repr ⟨Z i, hZ i⟩ c • (β c : ComplexMatrix2) :=
        Finset.sum_congr rfl fun c _ => by rw [hk c]
    _ = Z i := h
theorem logSeries_one : ComplexMatrix2.logSeries 1 = 0 := by
  simp [ComplexMatrix2.logSeries]
theorem exists_hasDerivAt_expCurve_and_realCurves
    (hh : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hel : ComplexMatrix2.ExpLogEstimates)
    (hlog : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      LeftChartFields.CurveLogDerivative ℝ I PeriodicLattice.complexGaugeGroup
        PeriodicLattice.complexLieAlgebra)
    {σ : Type} [Fintype σ] {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] {l : ℕ}
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : E ≃ Coordinates.ComplexCoordinates l)
    (eL : E ≃ₗ[ℂ] Coordinates.ComplexCoordinates l) (he : ∀ x, eL x = e x)
    {O : Set (σ → ComplexMatrix2)} {f : (σ → ComplexMatrix2) → E}
    (hf : IsHolomorphicToCoords β e (asGroupFactors '' O) fun p => f fun b => p (.inl b))
    {p₀ : σ → ComplexMatrix2} (hp : p₀ ∈ O)
    (hpG : ∀ s, p₀ s ∈ PeriodicLattice.complexGaugeGroup)
    {X : σ → ComplexMatrix2} (hX : ∀ s, X s ∈ ComplexMatrix2.traceless) :
    ∃ d : E, HasDerivAt
        (fun t : ℂ => f fun s => ComplexMatrix2.matExp (Complex.I • (t • X s)) * p₀ s) d 0 ∧
      ∀ w : ℝ → σ → ComplexMatrix2,
        (∀ᶠ t in 𝓝 (0 : ℝ), ∀ s, w t s ∈ PeriodicLattice.complexGaugeGroup) →
        w 0 = p₀ → HasDerivAt w (fun s => Complex.I • X s * p₀ s) 0 →
        HasDerivAt (fun t => f (w t)) d 0 := by
  classical
  obtain ⟨-, -, hpts⟩ := hf
  obtain ⟨O', h0, -, -, hH⟩ := hpts (asGroupFactors p₀) ⟨p₀, hp, rfl⟩
  let ν : (σ ⊕ Empty) ≃ Fin (Fintype.card (σ ⊕ Empty)) := Fintype.equivFin _
  let T := tupleOfCoords β ν
  obtain ⟨C, hC⟩ := exists_clm_tupleOfCoords_inverse β ν
  have hH' := hH ν
  have hT0 : T 0 = 0 := by
    funext i
    simp [T, tupleOfCoords, Coordinates.ComplexCoordinates.tracelessTuple]
  have h0Ω : (0 : Coordinates.ComplexCoordinates (Fintype.card (σ ⊕ Empty) * 3)) ∈
      tupleOfCoords β ν ⁻¹' O' := by
    change T 0 ∈ O'
    rw [hT0]
    exact h0
  obtain ⟨Lc, hL⟩ := ((hh.1 _ _ hH'.1).1 _ _ hH').2.2.1 0 h0Ω
  have hLc := hasFDerivAt_of_restrictScalars ℝ hL rfl
  let eC : Coordinates.ComplexCoordinates l →L[ℂ] E :=
    LinearMap.toContinuousLinearMap eL.symm.toLinearMap
  have heG : ∀ w, eC ((e ∘ ((fun p : σ ⊕ Empty → ComplexMatrix2 => f fun b => p (.inl b)) ∘
      expChartAt (asGroupFactors p₀)) ∘ tupleOfCoords β ν) w) =
      f fun s => expChartAt (asGroupFactors p₀) (T w) (.inl s) := by
    intro w
    change eL.symm (e _) = _
    rw [← he]
    exact eL.symm_apply_apply _
  let A₀ : σ ⊕ Empty → ComplexMatrix2 := asGroupFactors fun s => Complex.I • X s
  have hA₀ : ∀ i, A₀ i ∈ ComplexMatrix2.traceless := by
    rintro (s | e')
    · exact ComplexMatrix2.traceless.smul_mem _ (hX s)
    · exact e'.elim
  let w₀ := C A₀
  have hTw₀ : ∀ t : ℂ, T (t • w₀) = t • A₀ := by
    intro t
    have : t • w₀ = C (t • A₀) := (map_smul C t A₀).symm
    rw [this]
    exact hC _ fun i => ComplexMatrix2.traceless.smul_mem t (hA₀ i)
  refine ⟨eC (Lc w₀), ?_, ?_⟩
  · have hline : HasDerivAt (fun t : ℂ => t • w₀) w₀ 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const w₀
    have hat := hLc
    rw [← zero_smul ℂ w₀] at hat
    have h2 := hat.comp_hasDerivAt (0 : ℂ) hline
    have h3 := eC.hasFDerivAt.comp_hasDerivAt (0 : ℂ) h2
    refine h3.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply] at heG ⊢
    rw [heG, hTw₀]
    refine congrArg f (funext fun s => ?_)
    change ComplexMatrix2.matExp (Complex.I • (t • X s)) * p₀ s =
      ComplexMatrix2.matExp (t • Complex.I • X s) * p₀ s
    rw [smul_comm]
  · intro w hw h0' hd
    have hds : ∀ s, HasDerivAt (fun t => w t s) (Complex.I • X s * p₀ s) 0 :=
      fun s => hasDerivAt_pi.1 hd s
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hw
    have hI : IsOpenIntervalAroundZero (Metric.ball (0 : ℝ) ε) :=
      ⟨Metric.isOpen_ball, by rw [Real.ball_eq_Ioo]; exact ordConnected_Ioo,
        Metric.mem_ball_self hε⟩
    have hinv : ∀ s, p₀ s * (p₀ s)⁻¹ = 1 := fun s =>
      Matrix.mul_nonsing_inv _ (by
        have h : (p₀ s).det = 1 := hpG s
        rw [h]
        exact isUnit_one)
    have hinv' : ∀ s, (p₀ s)⁻¹ * p₀ s = 1 := fun s =>
      Matrix.nonsing_inv_mul _ (by
        have h : (p₀ s).det = 1 := hpG s
        rw [h]
        exact isUnit_one)
    have hZ : ∀ s, HasDerivAt (fun t => ComplexMatrix2.logSeries (w t s * (p₀ s)⁻¹))
        (Complex.I • X s) 0 := by
      intro s
      obtain ⟨-, hdiff, heq, -⟩ := hlog _ hI (fun t => w t s) (fun t ht => hball t ht s)
        (hds s).differentiableAt
      have h1 := smul_right_injective ComplexMatrix2 (inv_ne_zero Complex.I_ne_zero) heq
      simp only [h0', (hds s).deriv] at h1 hdiff
      have h2 := hdiff.hasDerivAt
      rw [h1, mul_assoc, hinv s, mul_one] at h2
      exact h2
    let Z : ℝ → σ ⊕ Empty → ComplexMatrix2 :=
      fun t => asGroupFactors fun s => ComplexMatrix2.logSeries (w t s * (p₀ s)⁻¹)
    have hZd : HasDerivAt Z A₀ 0 := by
      refine hasDerivAt_pi.2 ?_
      rintro (s | e')
      · exact hZ s
      · exact e'.elim
    have hZ0 : Z 0 = 0 := by
      funext i
      rcases i with s | e'
      · change ComplexMatrix2.logSeries (w 0 s * (p₀ s)⁻¹) = 0
        rw [h0', hinv s, logSeries_one]
      · exact e'.elim
    have hwt : HasDerivAt (fun t => C (Z t)) w₀ 0 :=
      (C.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hZd
    have hC0 : C (Z 0) = 0 := by
      rw [hZ0, map_zero]
    have hL0 := hL
    rw [← hC0] at hL0
    have h2 := hL0.comp_hasDerivAt (0 : ℝ) hwt
    have h3 := (eC.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
    refine h3.congr_of_eventuallyEq ?_
    have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ s,
        ComplexMatrix2.operatorNorm (w t s * (p₀ s)⁻¹ - 1) < 9 / 10 := by
      refine eventually_all.2 fun s => ?_
      have hc : ContinuousAt (fun t => w t s * (p₀ s)⁻¹ - 1) 0 :=
        ((hds s).continuousAt.mul continuousAt_const).sub continuousAt_const
      have hv : w 0 s * (p₀ s)⁻¹ - 1 = 0 := by
        rw [h0', hinv s, sub_self]
      have ht := hc.tendsto.norm
      simp only [hv, norm_zero] at ht
      exact ht.eventually (Iio_mem_nhds (by norm_num))
    filter_upwards [hw, hnear] with t h1 h2
    have hdet : ∀ s, (w t s * (p₀ s)⁻¹).det = 1 := by
      intro s
      have a : (w t s).det = 1 := h1 s
      have b : (p₀ s).det = 1 := hpG s
      rw [Matrix.det_mul, a, one_mul, Matrix.det_nonsing_inv, b]
      simp
    have hTZ : T (C (Z t)) = Z t := by
      refine hC _ ?_
      rintro (s | e')
      · exact (hel.2.2.2.2.2.2.1 _ (hdet s) (le_of_lt (h2 s))).2
      · exact e'.elim
    have hexp : ∀ s, ComplexMatrix2.matExp (ComplexMatrix2.logSeries (w t s * (p₀ s)⁻¹)) * p₀ s =
        w t s := by
      intro s
      have h4 := (hel.2.2.2.1 (w t s * (p₀ s)⁻¹ - 1)
        (by
          have := h2 s
          have h5 : ComplexMatrix2.operatorNorm (w t s * (p₀ s)⁻¹ - 1) < 1 := by linarith
          exact h5)).2.2.2.2
      rw [add_sub_cancel] at h4
      rw [h4, mul_assoc, hinv' s, mul_one]
    simp only [Function.comp_apply] at heG ⊢
    change f (w t) = eC _
    have := heG (C (Z t))
    rw [this, hTZ]
    refine congrArg f (funext fun s => ?_)
    exact (hexp s).symm
end Holomorphic
end Tower.FullSpaceCurveDifferentials
open Matrices
namespace Tower.FullSpace.CurveDerivatives
open UniqueValue Tower.FullSpaceCurveDifferentials
variable {L k j : ℕ}
def expPerturbation (𝕜 : Type) [NormedField 𝕜] [NormedAlgebra 𝕜 ℂ] (S : Finset (Edge L k j))
    (U B : Edge L k j → ComplexMatrix2) (t : 𝕜) : S → ComplexMatrix2 :=
  fun b => ComplexMatrix2.matExp (Complex.I • (algebraMap 𝕜 ℂ t • B b)) * U b
theorem perturbedTuple_zero_eq (𝕜 : Type) [NormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    (S : Finset (Edge L k j)) (U B : Edge L k j → ComplexMatrix2) (t : 𝕜) :
    perturbedTuple S B 0 U (algebraMap 𝕜 ℂ t) (algebraMap 𝕜 ℂ 0) = expPerturbation 𝕜 S U B t := by
  funext b
  simp [perturbedTuple, expPerturbation]
theorem expPerturbation_zero (𝕜 : Type) [NormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    (S : Finset (Edge L k j)) (U B : Edge L k j → ComplexMatrix2) :
    expPerturbation 𝕜 S U B 0 = restrictToEdges S U := by
  funext b
  simp [expPerturbation, restrictToEdges]
def HasCurveDerivative (𝕜 : Type) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {E : Type}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] (𝒢 : Set ComplexMatrix2)
    (S : Finset (Edge L k j)) (U B : Edge L k j → ComplexMatrix2)
    (f : (S → ComplexMatrix2) → E) : Prop :=
  ∃ d : E, HasDerivAt (fun t : 𝕜 => f (expPerturbation 𝕜 S U B t)) d 0 ∧
    ∀ w : ℝ → S → ComplexMatrix2, (∀ᶠ t in 𝓝 (0 : ℝ), w t ∈ edgeProduct 𝒢 S) →
      w 0 = restrictToEdges S U →
      HasDerivAt w (fun b => Complex.I • B b * U b) 0 → HasDerivAt (fun t => f (w t)) d 0
theorem hasCurveDerivative_real (hfp : FamilyProducts.FamilyProductsStatement)
    (hleft : (LeftChartFields.fullData L k j).LeftExpMulMemGroup)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Finset (Edge L k j)}
    {O : Set (S → ComplexMatrix2)} {f : (S → ComplexMatrix2) → E}
    {U B : Edge L k j → ComplexMatrix2}
    (hS : IsFinitePositiveEdgeSet S)
    (hf : EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower S) O f)
    (hp : restrictToEdges S U ∈ O) (hU : U ∈ fieldsValuedIn L k j PeriodicLattice.compactGaugeGroup)
    (hB : B ∈ edgeFormSpace (meshAt L k j)) :
    HasCurveDerivative ℝ PeriodicLattice.compactGaugeGroup S U B f := by
  have : Nonempty S := hS.1.to_subtype
  have hM : Submanifolds.IsSmoothSubmanifold (specialUnitaryPower S) := (hfp S).2.2
  have hpM : restrictToEdges S U ∈ specialUnitaryPower S := fun b => hU.1 b
  obtain ⟨d, hd⟩ := exists_hasDerivAt_comp_curve hM hf hp hpM
    (fun b : S => Complex.I • B b * U b)
  refine ⟨d, ?_, fun w hw h0 hdw => hd w hw h0 hdw⟩
  refine hd (expPerturbation ℝ S U B) (Eventually.of_forall fun t b => ?_)
    (expPerturbation_zero ℝ S U B) (hasDerivAt_pi.2 fun b => ?_)
  · exact (hleft.1 U hU B hB ⟨b.1, hS.2 b.1 b.2⟩).1 t
  · exact (hleft.1 U hU B hB ⟨b.1, hS.2 b.1 b.2⟩).2
theorem hasCurveDerivative_complex
    (hh : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hel : ComplexMatrix2.ExpLogEstimates)
    (hlog : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      LeftChartFields.CurveLogDerivative ℝ I PeriodicLattice.complexGaugeGroup
        PeriodicLattice.complexLieAlgebra)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] {l : ℕ}
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : E ≃ Coordinates.ComplexCoordinates l)
    (eL : E ≃ₗ[ℂ] Coordinates.ComplexCoordinates l) (he : ∀ x, eL x = e x)
    {S : Finset (Edge L k j)} {O : Set (S → ComplexMatrix2)} {f : (S → ComplexMatrix2) → E}
    {U B : Edge L k j → ComplexMatrix2} (hS : IsFinitePositiveEdgeSet S)
    (hf : holomorphicPresentations L k j β e S O f) (hp : restrictToEdges S U ∈ O)
    (hU : U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hB : IsComplexTangent B) :
    HasCurveDerivative ℂ PeriodicLattice.complexGaugeGroup S U B f := by
  obtain ⟨d, h1, h2⟩ := exists_hasDerivAt_expCurve_and_realCurves hh hel hlog β e eL he hf hp
    (fun b => hU.1 b) (X := fun b : S => B b) (fun b => hB b (hS.2 b.1 b.2))
  exact ⟨d, h1, fun w hw h0 hdw => h2 w hw h0 hdw⟩
theorem exists_deriv_chosenPresentation (𝕜 : Type) [NontriviallyNormedField 𝕜]
    [NormedAlgebra 𝕜 ℂ] {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
    [Nonempty E] {𝒢 : Set ComplexMatrix2} {𝔇 : Set (Edge L k j → ComplexMatrix2)}
    {K : PresentationClass L k j E}
    {h : (Edge L k j → ComplexMatrix2) → E} {U B : Edge L k j → ComplexMatrix2}
    (hex : ∃ (F : Finset (Edge L k j)) (O : Set (F → ComplexMatrix2))
      (f : (F → ComplexMatrix2) → E), IsLocalPresentation 𝒢 𝔇 h U F O f ∧ K F O f)
    (hsee : ∀ (F : Finset (Edge L k j)) (O : Set (F → ComplexMatrix2))
      (f : (F → ComplexMatrix2) → E),
      IsLocalPresentation 𝒢 𝔇 h U F O f → K F O f → HasCurveDerivative 𝕜 𝒢 F U B f)
    (hone : ∀ (F₁ : Finset (Edge L k j)) (O₁ : Set (F₁ → ComplexMatrix2))
      (f₁ : (F₁ → ComplexMatrix2) → E)
      (F₂ : Finset (Edge L k j)) (O₂ : Set (F₂ → ComplexMatrix2))
      (f₂ : (F₂ → ComplexMatrix2) → E),
      IsLocalPresentation 𝒢 𝔇 h U F₁ O₁ f₁ → IsLocalPresentation 𝒢 𝔇 h U F₂ O₂ f₂ →
        AgreeAlongPerturbations 𝕜 U B 0 F₁ O₁ f₁ F₂ O₂ f₂) :
    ∃ d : E, HasDerivAt
        (fun t : 𝕜 => valueViaPresentation 𝒢 𝔇 K h U (algebraMap 𝕜 ℂ t • B)) d 0 ∧
      ∀ (F : Finset (Edge L k j)) (O : Set (F → ComplexMatrix2)) (f : (F → ComplexMatrix2) → E),
        IsLocalPresentation 𝒢 𝔇 h U F O f → K F O f → ∀ w : ℝ → F → ComplexMatrix2,
          (∀ᶠ t in 𝓝 (0 : ℝ), w t ∈ edgeProduct 𝒢 F) → w 0 = restrictToEdges F U →
          HasDerivAt w (fun b => Complex.I • B b * U b) 0 →
          HasDerivAt (fun t => f (w t)) d 0 := by
  have hspec : IsLocalPresentation 𝒢 𝔇 h U (chosenPresentation 𝒢 𝔇 K h U).support
      (chosenPresentation 𝒢 𝔇 K h U).region (chosenPresentation 𝒢 𝔇 K h U).fn ∧
      K (chosenPresentation 𝒢 𝔇 K h U).support (chosenPresentation 𝒢 𝔇 K h U).region
        (chosenPresentation 𝒢 𝔇 K h U).fn :=
    Classical.epsilon_spec (p := fun w : LocalData L k j E =>
      IsLocalPresentation 𝒢 𝔇 h U w.support w.region w.fn ∧ K w.support w.region w.fn) (by
        obtain ⟨F, O, f, h1, h2⟩ := hex
        exact ⟨⟨F, O, f⟩, h1, h2⟩)
  obtain ⟨d, hd, -⟩ := hsee _ _ _ hspec.1 hspec.2
  refine ⟨d, hd, fun F O f hw hk w h1 h2 h3 => ?_⟩
  obtain ⟨d', hd', hc'⟩ := hsee F O f hw hk
  have heq : d' = d := by
    obtain ⟨ε, hε, hall⟩ := hone _ _ _ _ _ _ hw hspec.1
    have hev : (fun t : 𝕜 => f (expPerturbation 𝕜 F U B t)) =ᶠ[𝓝 0] fun t : 𝕜 =>
        (chosenPresentation 𝒢 𝔇 K h U).fn
          (expPerturbation 𝕜 (chosenPresentation 𝒢 𝔇 K h U).support U B t) := by
      filter_upwards [Metric.ball_mem_nhds (0 : 𝕜) hε] with t ht
      have h4 := (hall t 0 (by simpa using ht) (by simpa using hε)).2.2
      rwa [perturbedTuple_zero_eq, perturbedTuple_zero_eq] at h4
    exact (hd'.congr_of_eventuallyEq hev.symm).unique hd
  rw [← heq]
  exact hc' w h1 h2 h3
theorem chosenPresentation_values_mem (𝕜 : Type) [NontriviallyNormedField 𝕜]
    [NormedAlgebra 𝕜 ℂ] {𝒢 : Set ComplexMatrix2} {kept : Set (Set ComplexMatrix2)}
    {𝔇 : Set (Edge L k j → ComplexMatrix2)} {K : PresentationClass L k j ComplexMatrix2}
    {h : (Edge L k j → ComplexMatrix2) → ComplexMatrix2} {U B : Edge L k j → ComplexMatrix2}
    (hex : ∃ (F : Finset (Edge L k j)) (O : Set (F → ComplexMatrix2))
      (f : (F → ComplexMatrix2) → ComplexMatrix2), IsLocalPresentation 𝒢 𝔇 h U F O f ∧ K F O f)
    (hU : U ∈ 𝔇) (hkept : 𝒢 ∈ kept) (hval : ∀ U' ∈ 𝔇, h U' ∈ 𝒢)
    (hdim : LocalPresentations.PresentationShrinks 𝒢 kept 𝔇 h U)
    (hone : ∀ (F₁ : Finset (Edge L k j)) (O₁ : Set (F₁ → ComplexMatrix2))
      (f₁ : (F₁ → ComplexMatrix2) → ComplexMatrix2)
      (F₂ : Finset (Edge L k j)) (O₂ : Set (F₂ → ComplexMatrix2))
      (f₂ : (F₂ → ComplexMatrix2) → ComplexMatrix2),
      IsLocalPresentation 𝒢 𝔇 h U F₁ O₁ f₁ → IsLocalPresentation 𝒢 𝔇 h U F₂ O₂ f₂ →
        AgreeAlongPerturbations 𝕜 U B 0 F₁ O₁ f₁ F₂ O₂ f₂) :
    (∃ ε : ℝ, 0 < ε ∧ MapsTo
      (fun t : 𝕜 => valueViaPresentation 𝒢 𝔇 K h U (algebraMap 𝕜 ℂ t • B))
      (Metric.ball 0 ε) 𝒢) ∧
    valueViaPresentation 𝒢 𝔇 K h U (algebraMap 𝕜 ℂ 0 • B) = h U := by
  have hspec : IsLocalPresentation 𝒢 𝔇 h U (chosenPresentation 𝒢 𝔇 K h U).support
      (chosenPresentation 𝒢 𝔇 K h U).region (chosenPresentation 𝒢 𝔇 K h U).fn ∧
      K (chosenPresentation 𝒢 𝔇 K h U).support (chosenPresentation 𝒢 𝔇 K h U).region
        (chosenPresentation 𝒢 𝔇 K h U).fn :=
    Classical.epsilon_spec (p := fun w : LocalData L k j ComplexMatrix2 =>
      IsLocalPresentation 𝒢 𝔇 h U w.support w.region w.fn ∧ K w.support w.region w.fn) (by
        obtain ⟨F, O, f, h1, h2⟩ := hex
        exact ⟨⟨F, O, f⟩, h1, h2⟩)
  obtain ⟨⟨O', hO', hsub, hpt, -, hk⟩, hdim2⟩ := hdim _ _ _ hspec.1
  have hw' : IsLocalPresentation 𝒢 𝔇 h U (chosenPresentation 𝒢 𝔇 K h U).support O'
      (chosenPresentation 𝒢 𝔇 K h U).fn := hdim2 O' hO' hsub hpt _ fun _ _ => rfl
  obtain ⟨ε, hε, hall⟩ := hone _ _ _ _ _ _ hw' hw'
  refine ⟨⟨ε, hε, fun t ht => ?_⟩, ?_⟩
  · have h4 := (hall t 0 (by simpa using ht) (by simpa using hε)).1
    rw [perturbedTuple_zero_eq] at h4
    exact hk 𝒢 hkept hval _ h4
  · have h5 : (chosenPresentation 𝒢 𝔇 K h U).fn
        (expPerturbation 𝕜 (chosenPresentation 𝒢 𝔇 K h U).support U B 0) = h U := by
      rw [expPerturbation_zero]
      exact (hspec.1.2.2.2 U hU hspec.1.2.2.1).symm
    exact h5
theorem I_smul_logDirectionalDeriv_real {𝒢 𝔥 : Set ComplexMatrix2}
    {φ : (Edge L k j → ComplexMatrix2) → ComplexMatrix2}
    {W d : ComplexMatrix2} {B : Edge L k j → ComplexMatrix2} {ε : ℝ}
    (hlog : LeftChartFields.CurveLogDerivative ℝ (Metric.ball 0 ε) 𝒢 𝔥)
    (hmem : MapsTo (fun t : ℝ => φ (algebraMap ℝ ℂ t • B)) (Metric.ball 0 ε) 𝒢)
    (h0 : φ (algebraMap ℝ ℂ 0 • B) = W)
    (hd : HasDerivAt (fun t : ℝ => φ (algebraMap ℝ ℂ t • B)) d 0) :
    Complex.I • logDirectionalDeriv ℝ φ W B = d * W⁻¹ := by
  obtain ⟨-, -, heq, -⟩ := hlog _ hmem hd.differentiableAt
  simp only [h0] at heq
  rw [hd.deriv] at heq
  change Complex.I • (Complex.I⁻¹ •
    deriv (fun t : ℝ => ComplexMatrix2.logSeries (φ (algebraMap ℝ ℂ t • B) * W⁻¹)) 0) = _
  rw [heq, smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul]
theorem I_smul_logDirectionalDeriv_complex {𝒢 𝔥 : Set ComplexMatrix2}
    {φ : (Edge L k j → ComplexMatrix2) → ComplexMatrix2}
    {W d : ComplexMatrix2} {B : Edge L k j → ComplexMatrix2} {ε : ℝ}
    (hlog : LeftChartFields.CurveLogDerivative ℂ (Metric.ball 0 ε) 𝒢 𝔥)
    (hmem : MapsTo (fun t : ℂ => φ (algebraMap ℂ ℂ t • B)) (Metric.ball 0 ε) 𝒢)
    (h0 : φ (algebraMap ℂ ℂ 0 • B) = W)
    (hd : HasDerivAt (fun t : ℂ => φ (algebraMap ℂ ℂ t • B)) d 0) :
    Complex.I • logDirectionalDeriv ℂ φ W B = d * W⁻¹ := by
  obtain ⟨-, -, heq, -⟩ := hlog _ hmem hd.differentiableAt
  simp only [h0] at heq
  rw [hd.deriv] at heq
  change Complex.I • (Complex.I⁻¹ •
    deriv (fun t : ℂ => ComplexMatrix2.logSeries (φ (algebraMap ℂ ℂ t • B) * W⁻¹)) 0) = _
  rw [heq, smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul]
section Curves
variable {𝒢 : Set ComplexMatrix2} {I : Set ℝ} {γ : ℝ → Edge L k j → ComplexMatrix2}
  {U : Edge L k j → ComplexMatrix2}
theorem domain_mem_nhds_zero (hγ : IsDifferentiableFieldCurve 𝒢 I γ) : I ∈ 𝓝 (0 : ℝ) :=
  hγ.1.1.mem_nhds hγ.1.2.2
theorem tendsto_restrictToEdges (hγ : IsDifferentiableFieldCurve 𝒢 I γ) (h0 : γ 0 = U)
    {F : Finset (Edge L k j)} (hF : IsFinitePositiveEdgeSet F) :
    Tendsto (fun t => restrictToEdges F (γ t)) (𝓝 0) (𝓝 (restrictToEdges F U)) := by
  refine tendsto_pi_nhds.2 fun b => ?_
  have h1 := ((hγ.2.2 b.1 (hF.2 b.1 b.2)).differentiableAt
    (domain_mem_nhds_zero hγ)).continuousAt.tendsto
  simpa [restrictToEdges, h0] using h1
theorem eventually_restrictToEdges_mem (hγ : IsDifferentiableFieldCurve 𝒢 I γ)
    (F : Finset (Edge L k j)) :
    ∀ᶠ t in 𝓝 (0 : ℝ), restrictToEdges F (γ t) ∈ edgeProduct 𝒢 F := by
  filter_upwards [domain_mem_nhds_zero hγ] with t ht
  exact fun b => (hγ.2.1 ht).1 b
theorem eventually_restrictToEdges_mem_open (hγ : IsDifferentiableFieldCurve 𝒢 I γ)
    (h0 : γ 0 = U) {F : Finset (Edge L k j)} (hF : IsFinitePositiveEdgeSet F)
    {O : Set (F → ComplexMatrix2)}
    (hO : ComplexMatrix2.IsRelativelyOpen (edgeProduct 𝒢 F) O) (hp : restrictToEdges F U ∈ O) :
    ∀ᶠ t in 𝓝 (0 : ℝ), restrictToEdges F (γ t) ∈ O := by
  obtain ⟨O', hO', heq⟩ := hO
  rw [heq] at hp ⊢
  filter_upwards [tendsto_restrictToEdges hγ h0 hF (hO'.mem_nhds hp.1),
    eventually_restrictToEdges_mem hγ F] with t h1 h2
  exact ⟨h1, h2⟩
theorem presentationValuesAlongCurve {E : Type} {𝔇 : Set (Edge L k j → ComplexMatrix2)}
    {K : PresentationClass L k j E} {h : (Edge L k j → ComplexMatrix2) → E}
    (hagree : LocalPresentations.PresentationsAgree 𝒢 𝔇 h U)
    (hγ : IsDifferentiableFieldCurve 𝒢 I γ) (h0 : γ 0 = U) :
    LeftChartFacts.PresentationValuesAlongCurve 𝒢 𝔇 K h U γ := by
  classical
  refine ⟨fun S O f hw _ => eventually_restrictToEdges_mem_open hγ h0 hw.1 hw.2.1 hw.2.2.1,
    fun S₁ O₁ f₁ S₂ O₂ f₂ hw₁ _ hw₂ _ => ?_,
    fun S O f hw _ t hO hD => (hw.2.2.2 _ hD hO).symm⟩
  have hF : IsFinitePositiveEdgeSet (S₁ ∪ S₂) :=
    ⟨hw₁.1.1.mono Finset.subset_union_left, fun b hb => by
      rcases Finset.mem_union.1 hb with hb | hb
      · exact hw₁.1.2 b hb
      · exact hw₂.1.2 b hb⟩
  obtain ⟨ε, hε, hall⟩ := hagree S₁ S₂ (S₁ ∪ S₂) O₁ O₂ f₁ f₂ Finset.subset_union_left
    Finset.subset_union_right hF hw₁ hw₂
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ b : ↥(S₁ ∪ S₂),
      ComplexMatrix2.operatorNorm (restrictToEdges (S₁ ∪ S₂) (γ t) b - U b) < ε := by
    refine eventually_all.2 fun b => ?_
    have hb := tendsto_pi_nhds.1 (tendsto_restrictToEdges hγ h0 hF) b
    have h1 := Metric.tendsto_nhds.1 hb ε hε
    filter_upwards [h1] with t ht
    rwa [dist_eq_norm] at ht
  filter_upwards [hnear, eventually_restrictToEdges_mem hγ (S₁ ∪ S₂)] with t h1 h2
  obtain ⟨-, -, -, e1, e2⟩ := hall _ h2 h1
  exact e1.trans e2.symm
theorem hasDerivAt_restrictToEdges (hγ : IsDifferentiableFieldCurve 𝒢 I γ) (h0 : γ 0 = U)
    (hG : 𝒢 ⊆ PeriodicLattice.complexGaugeGroup) {F : Finset (Edge L k j)}
    (hF : IsFinitePositiveEdgeSet F) :
    HasDerivAt (fun t => restrictToEdges F (γ t))
      (fun b : F => Complex.I • curveTangent γ b * U b) 0 := by
  refine hasDerivAt_pi.2 fun b => ?_
  have hb : (b : Edge L k j).IsPositivelyOriented := hF.2 b.1 b.2
  have hdiff := ((hγ.2.2 b.1 hb).differentiableAt (domain_mem_nhds_zero hγ)).hasDerivAt
  have e : curveTangent γ b.1 =
      Complex.I⁻¹ • (deriv (fun t => γ t b.1) 0 * (γ 0 b.1)⁻¹) := if_pos hb
  have hdet : (U b.1).det = 1 := by
    have h1 : γ 0 b.1 ∈ 𝒢 := (hγ.2.1 hγ.1.2.2).1 b.1
    rw [h0] at h1
    exact hG h1
  have hval : Complex.I • curveTangent γ b.1 * U b.1 = deriv (fun t => γ t b.1) 0 := by
    rw [e, smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul, h0, mul_assoc,
      Matrix.nonsing_inv_mul _ (by rw [hdet]; exact isUnit_one), mul_one]
  change HasDerivAt (fun t => γ t b.1) (Complex.I • curveTangent γ b.1 * U b.1) 0
  rw [hval]
  exact hdiff
theorem extendOddly_opposite {a : ℝ} (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    (b : InfiniteLattice.Link a) : extendOddly f b.opposite = -extendOddly f b := by
  have h := InfiniteLattice.xor_mem_positiveLinks ha b
  simp only [InfiniteLattice.mem_positiveLinks_iff] at h
  have hrr : b.opposite.opposite = b := rfl
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have e1 : extendOddly f b.opposite = -f b.opposite.opposite := if_neg h₂
    have e2 : extendOddly f b = f b := if_pos h₁
    rw [e1, e2, hrr]
  · have e1 : extendOddly f b.opposite = f b.opposite := if_pos h₁
    have e2 : extendOddly f b = -f b.opposite := if_neg h₂
    rw [e1, e2, neg_neg]
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.meshAt_pos <;> assumption
theorem curveTangent_mem {𝔥 : Set ComplexMatrix2}
    (hlog : LeftChartFields.CurveLogDerivative ℝ I 𝒢 𝔥)
    (hγ : IsDifferentiableFieldCurve 𝒢 I γ) {b : Edge L k j} (hb : b.IsPositivelyOriented) :
    curveTangent γ b ∈ 𝔥 := by
  have e : curveTangent γ b = Complex.I⁻¹ • (deriv (fun t => γ t b) 0 * (γ 0 b)⁻¹) := if_pos hb
  rw [e]
  exact (hlog (fun t => γ t b) (fun t ht => (hγ.2.1 ht).1 b)
    ((hγ.2.2 b hb).differentiableAt (domain_mem_nhds_zero hγ))).2.2.2
end Curves
section Requirements
variable {j' : ℕ}
def matrixLinearEquiv : ComplexMatrix2 ≃ₗ[ℂ] Coordinates.ComplexCoordinates 4 :=
  { Coordinates.ComplexCoordinates.matrixEquiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
theorem compactGaugeGroup_subset :
    PeriodicLattice.compactGaugeGroup ⊆ PeriodicLattice.complexGaugeGroup :=
  fun _ h => (Matrix.mem_specialUnitaryGroup_iff.1 h).2
theorem curveTangent_mem_edgeFormSpace (hL : Conventions.IsAdmissibleBlockingFactor L)
    {I : Set ℝ} {γ : ℝ → Edge L k j → ComplexMatrix2}
    (hlog : LeftChartFields.CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup
      PeriodicLattice.compactLieAlgebra)
    (hγ : IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ) :
    curveTangent γ ∈ edgeFormSpace (meshAt L k j) :=
  ⟨fun _ hb => curveTangent_mem hlog hγ hb,
    fun b => extendOddly_opposite (meshAt_pos hL) _ b⟩
theorem isOpenIntervalAroundZero_ball {ε : ℝ} (hε : 0 < ε) :
    IsOpenIntervalAroundZero (Metric.ball (0 : ℝ) ε) :=
  ⟨Metric.isOpen_ball, by rw [Real.ball_eq_Ioo]; exact ordConnected_Ioo, Metric.mem_ball_self hε⟩
theorem fnDerivAlongCurves_real (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hfp : FamilyProducts.FamilyProductsStatement)
    (hleft : (LeftChartFields.fullData L k j).LeftExpMulMemGroup)
    (hlog : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      LeftChartFields.CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup
        PeriodicLattice.compactLieAlgebra)
    (hold : LocalPresentations.NearPointProperties L k j PeriodicLattice.compactGaugeGroup
      {LocalPresentations.realLine})
    (hone : PresentationsAgreeAlongPerturbations L k j ℝ PeriodicLattice.compactGaugeGroup
      (fun B => B ∈ edgeFormSpace (meshAt L k j)) ℂ)
    {𝔇 : Set (Edge L k j → ComplexMatrix2)} {F : (Edge L k j → ComplexMatrix2) → ℂ}
    (hF : IsDifferentiableFn 𝔇 F) {U : Edge L k j → ComplexMatrix2} (hU : U ∈ 𝔇) :
    LeftChartFacts.FnDerivAlongCurves PeriodicLattice.compactGaugeGroup 𝔇
      (differentiablePresentations L k j ℂ) F U (leftDeriv 𝔇 F U) := by
  intro I γ hγ h0
  have hUc : U ∈ fieldsValuedIn L k j PeriodicLattice.compactGaugeGroup := hF.1.1 hU
  have hB := curveTangent_mem_edgeFormSpace hL (hlog I hγ.1) hγ
  obtain ⟨-, hagree, -⟩ := hold 𝔇 F U hF.1 hU
  obtain ⟨d, hd, hc⟩ := exists_deriv_chosenPresentation ℝ
    (𝒢 := PeriodicLattice.compactGaugeGroup) (𝔇 := 𝔇)
    (K := differentiablePresentations L k j ℂ) (h := F) (U := U) (B := curveTangent γ)
    (hF.2.2 U hU)
    (fun S O f hw hk => hasCurveDerivative_real hfp hleft hw.1 hk hw.2.2.1 hUc hB)
    (fun F₁ O₁ f₁ F₂ O₂ f₂ h₁ h₂ =>
      hone 𝔇 hF.1 F U hU F₁ O₁ f₁ F₂ O₂ f₂ h₁ h₂ _ 0 hB (Submodule.zero_mem _))
  refine ⟨presentationValuesAlongCurve hagree hγ h0, fun S O f hw hk => ?_⟩
  have hval : leftDeriv 𝔇 F U (curveTangent γ) = d := hd.deriv
  rw [hval]
  exact hc S O f hw hk _ (eventually_restrictToEdges_mem hγ S)
    (congrArg (restrictToEdges S) h0)
    (hasDerivAt_restrictToEdges hγ h0 compactGaugeGroup_subset hw.1)
theorem mapDerivAlongCurves_real (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hfp : FamilyProducts.FamilyProductsStatement)
    (hleft : (LeftChartFields.fullData L k j).LeftExpMulMemGroup)
    (hlog : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      LeftChartFields.CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup
        PeriodicLattice.compactLieAlgebra)
    (hold : LocalPresentations.NearPointProperties L k j PeriodicLattice.compactGaugeGroup
      {LocalPresentations.realEntryMatrices, PeriodicLattice.compactGaugeGroup})
    (hone : PresentationsAgreeAlongPerturbations L k j ℝ PeriodicLattice.compactGaugeGroup
      (fun B => B ∈ edgeFormSpace (meshAt L k j)) ComplexMatrix2)
    {𝔇 : Set (Edge L k j → ComplexMatrix2)}
    {m : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2}
    (hm : IsDifferentiableFieldMap 𝔇 m) {U : Edge L k j → ComplexMatrix2} (hU : U ∈ 𝔇) :
    LeftChartFacts.MapDerivAlongCurves PeriodicLattice.compactGaugeGroup 𝔇
      (differentiablePresentations L k j ComplexMatrix2) m U (leftDifferential 𝔇 m U) := by
  intro I γ hγ h0 c hc
  have hUc : U ∈ fieldsValuedIn L k j PeriodicLattice.compactGaugeGroup := hm.1.1 hU
  have hB := curveTangent_mem_edgeFormSpace hL (hlog I hγ.1) hγ
  obtain ⟨-, hagree, hdim⟩ := hold 𝔇 (fun U' => m U' c) U hm.1 hU
  have hex := (hm.2.2 c hc).2 U hU
  have hone' : ∀ (F₁ : Finset (Edge L k j)) (O₁ : Set (F₁ → ComplexMatrix2))
      (f₁ : (F₁ → ComplexMatrix2) → ComplexMatrix2) (F₂ : Finset (Edge L k j))
      (O₂ : Set (F₂ → ComplexMatrix2)) (f₂ : (F₂ → ComplexMatrix2) → ComplexMatrix2),
      IsLocalPresentation PeriodicLattice.compactGaugeGroup 𝔇 (fun U' => m U' c) U F₁ O₁ f₁ →
      IsLocalPresentation PeriodicLattice.compactGaugeGroup 𝔇 (fun U' => m U' c) U F₂ O₂ f₂ →
        AgreeAlongPerturbations ℝ U (curveTangent γ) 0 F₁ O₁ f₁ F₂ O₂ f₂ :=
    fun F₁ O₁ f₁ F₂ O₂ f₂ h₁ h₂ =>
      hone 𝔇 hm.1 (fun U' => m U' c) U hU F₁ O₁ f₁ F₂ O₂ f₂ h₁ h₂ _ 0 hB (Submodule.zero_mem _)
  obtain ⟨d, hd, hcv⟩ := exists_deriv_chosenPresentation ℝ
    (𝒢 := PeriodicLattice.compactGaugeGroup) (𝔇 := 𝔇)
    (K := differentiablePresentations L k j ComplexMatrix2) (h := fun U' => m U' c) (U := U)
    (B := curveTangent γ) hex
    (fun S O f hw hk => hasCurveDerivative_real hfp hleft hw.1 hk hw.2.2.1 hUc hB) hone'
  obtain ⟨⟨ε, hε, hmem⟩, hg0⟩ := chosenPresentation_values_mem ℝ
    (K := differentiablePresentations L k j ComplexMatrix2) (B := curveTangent γ) hex hU
    (Or.inr rfl) (fun U' hU' => (hm.2.1 hU').1 c) hdim hone'
  have hform := I_smul_logDirectionalDeriv_real (hlog _ (isOpenIntervalAroundZero_ball hε))
    hmem hg0 hd
  refine ⟨presentationValuesAlongCurve hagree hγ h0, fun S O f hw hk => ?_⟩
  have hvalue : leftDifferential 𝔇 m U (curveTangent γ) c = logDirectionalDeriv ℝ
      (valueViaPresentation PeriodicLattice.compactGaugeGroup 𝔇
        (differentiablePresentations L k j ComplexMatrix2)
        (fun U' => m U' c) U) (m U c) (curveTangent γ) := if_pos hc
  rw [hvalue, hform]
  exact (hcv S O f hw hk _ (eventually_restrictToEdges_mem hγ S)
    (congrArg (restrictToEdges S) h0)
    (hasDerivAt_restrictToEdges hγ h0 compactGaugeGroup_subset hw.1)).mul_const _
theorem fnDerivAlongCurves_holomorphic
    (hh : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hel : ComplexMatrix2.ExpLogEstimates)
    (hlog : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      LeftChartFields.CurveLogDerivative ℝ I PeriodicLattice.complexGaugeGroup
        PeriodicLattice.complexLieAlgebra)
    (hold : LocalPresentations.NearPointProperties L k j PeriodicLattice.complexGaugeGroup
      {LocalPresentations.realLine})
    (hone : PresentationsAgreeAlongPerturbations L k j ℂ PeriodicLattice.complexGaugeGroup
      IsComplexTangent ℂ)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {𝔇 : Set (Edge L k j → ComplexMatrix2)} {F : (Edge L k j → ComplexMatrix2) → ℂ}
    (hF : IsHolomorphicFn β (Equiv.funUnique (Fin 1) ℂ).symm 𝔇 F)
    {U : Edge L k j → ComplexMatrix2} (hU : U ∈ 𝔇) :
    LeftChartFacts.FnDerivAlongCurves PeriodicLattice.complexGaugeGroup 𝔇
      (holomorphicPresentations L k j β (Equiv.funUnique (Fin 1) ℂ).symm) F U
      (holLeftDeriv β (Equiv.funUnique (Fin 1) ℂ).symm 𝔇 F U) := by
  intro I γ hγ h0
  have hUc : U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup := hF.1.1 hU
  have hB : IsComplexTangent (curveTangent γ) :=
    fun _ hb => curveTangent_mem (hlog I hγ.1) hγ hb
  obtain ⟨-, hagree, -⟩ := hold 𝔇 F U hF.1 hU
  obtain ⟨d, hd, hc⟩ := exists_deriv_chosenPresentation ℂ
    (𝒢 := PeriodicLattice.complexGaugeGroup) (𝔇 := 𝔇)
    (K := holomorphicPresentations L k j β (Equiv.funUnique (Fin 1) ℂ).symm) (h := F) (U := U)
    (B := curveTangent γ) (hF.2.2 U hU)
    (fun S O f hw hk => hasCurveDerivative_complex hh hel hlog β _
      (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm (fun _ => rfl) hw.1 hk hw.2.2.1 hUc hB)
    (fun F₁ O₁ f₁ F₂ O₂ f₂ h₁ h₂ => hone 𝔇 hF.1 F U hU F₁ O₁ f₁ F₂ O₂ f₂ h₁ h₂ _ 0 hB
      fun _ _ => ComplexMatrix2.traceless.zero_mem)
  refine ⟨presentationValuesAlongCurve hagree hγ h0, fun S O f hw hk => ?_⟩
  have hval : holLeftDeriv β (Equiv.funUnique (Fin 1) ℂ).symm 𝔇 F U
      (curveTangent γ) = d := hd.deriv
  rw [hval]
  exact hc S O f hw hk _ (eventually_restrictToEdges_mem hγ S)
    (congrArg (restrictToEdges S) h0)
    (hasDerivAt_restrictToEdges hγ h0 subset_rfl hw.1)
theorem mapDerivAlongCurves_holomorphic
    (hh : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hel : ComplexMatrix2.ExpLogEstimates)
    (hlog : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      LeftChartFields.CurveLogDerivative ℝ I PeriodicLattice.complexGaugeGroup
        PeriodicLattice.complexLieAlgebra)
    (hlogc : ∀ ρ : ℝ, 0 < ρ →
      LeftChartFields.CurveLogDerivative ℂ (Metric.ball 0 ρ)
        PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra)
    (hold : LocalPresentations.NearPointProperties L k j PeriodicLattice.complexGaugeGroup
      {LocalPresentations.realEntryMatrices, PeriodicLattice.complexGaugeGroup})
    (hone : PresentationsAgreeAlongPerturbations L k j ℂ PeriodicLattice.complexGaugeGroup
      IsComplexTangent ComplexMatrix2)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {𝔇 : Set (Edge L k j → ComplexMatrix2)}
    {m : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2}
    (hm : IsHolomorphicFieldMap β 𝔇 m) {U : Edge L k j → ComplexMatrix2} (hU : U ∈ 𝔇) :
    LeftChartFacts.MapDerivAlongCurves PeriodicLattice.complexGaugeGroup 𝔇
      (holomorphicPresentations L k j β Coordinates.ComplexCoordinates.matrixEquiv) m U
      (holLeftDifferential β 𝔇 m U) := by
  intro I γ hγ h0 c hc
  have hUc : U ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup := hm.1.1 hU
  have hB : IsComplexTangent (curveTangent γ) :=
    fun _ hb => curveTangent_mem (hlog I hγ.1) hγ hb
  obtain ⟨-, hagree, hdim⟩ := hold 𝔇 (fun U' => m U' c) U hm.1 hU
  have hex := (hm.2.2 c hc).2 U hU
  have hone' : ∀ (F₁ : Finset (Edge L k j)) (O₁ : Set (F₁ → ComplexMatrix2))
      (f₁ : (F₁ → ComplexMatrix2) → ComplexMatrix2) (F₂ : Finset (Edge L k j))
      (O₂ : Set (F₂ → ComplexMatrix2)) (f₂ : (F₂ → ComplexMatrix2) → ComplexMatrix2),
      IsLocalPresentation PeriodicLattice.complexGaugeGroup 𝔇 (fun U' => m U' c) U F₁ O₁ f₁ →
      IsLocalPresentation PeriodicLattice.complexGaugeGroup 𝔇 (fun U' => m U' c) U F₂ O₂ f₂ →
        AgreeAlongPerturbations ℂ U (curveTangent γ) 0 F₁ O₁ f₁ F₂ O₂ f₂ :=
    fun F₁ O₁ f₁ F₂ O₂ f₂ h₁ h₂ =>
      hone 𝔇 hm.1 (fun U' => m U' c) U hU F₁ O₁ f₁ F₂ O₂ f₂ h₁ h₂ _ 0 hB
        fun _ _ => ComplexMatrix2.traceless.zero_mem
  obtain ⟨d, hd, hcv⟩ := exists_deriv_chosenPresentation ℂ
    (𝒢 := PeriodicLattice.complexGaugeGroup) (𝔇 := 𝔇)
    (K := holomorphicPresentations L k j β Coordinates.ComplexCoordinates.matrixEquiv)
    (h := fun U' => m U' c) (U := U) (B := curveTangent γ) hex
    (fun S O f hw hk => hasCurveDerivative_complex hh hel hlog β _ matrixLinearEquiv
      (fun _ => rfl) hw.1 hk hw.2.2.1 hUc hB) hone'
  obtain ⟨⟨ε, hε, hmem⟩, hg0⟩ := chosenPresentation_values_mem ℂ
    (K := holomorphicPresentations L k j β Coordinates.ComplexCoordinates.matrixEquiv)
    (B := curveTangent γ) hex hU (Or.inr rfl) (fun U' hU' => (hm.2.1 hU').1 c) hdim hone'
  have hform := I_smul_logDirectionalDeriv_complex (hlogc _ hε) hmem hg0 hd
  refine ⟨presentationValuesAlongCurve hagree hγ h0, fun S O f hw hk => ?_⟩
  have hvalue : holLeftDifferential β 𝔇 m U (curveTangent γ) c =
      logDirectionalDeriv ℂ (valueViaPresentation PeriodicLattice.complexGaugeGroup 𝔇
        (holomorphicPresentations L k j β Coordinates.ComplexCoordinates.matrixEquiv)
        (fun U' => m U' c) U) (m U c) (curveTangent γ) := if_pos hc
  rw [hvalue, hform]
  exact (hcv S O f hw hk _ (eventually_restrictToEdges_mem hγ S)
    (congrArg (restrictToEdges S) h0)
    (hasDerivAt_restrictToEdges hγ h0 subset_rfl hw.1)).mul_const _
end Requirements
end Tower.FullSpace.CurveDerivatives
namespace Tower.FullSpaceCurveDifferentials
open Tower.FullSpace.CurveDerivatives
theorem statement_holds (hV : LocalPresentations.LocalPresentationNearPoint)
    (hOne : Tower.FullSpace.UniqueValue.PresentationsAgreeAndBallsOpen)
    (hA : LeftChartFields.Claim)
    (hfp : FamilyProducts.FamilyProductsStatement)
    (hel : ComplexMatrix2.ExpLogEstimates)
    (hh : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) : Statement := by
  intro L k j j' hL hj _
  obtain ⟨hv₁, hv₂, hv₃, hv₄⟩ := hV L hL k j hj
  obtain ⟨ho₁, ho₂, ho₃, ho₄⟩ := (hOne L k j hL.1 hL.2 hj).1
  have hleft := (hA.2.2 L k j hL hj).2.1.1
  have hlr : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      LeftChartFields.CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup
        PeriodicLattice.compactLieAlgebra := fun I hI => (hA.1 I hI).1
  have hlc : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
      LeftChartFields.CurveLogDerivative ℝ I PeriodicLattice.complexGaugeGroup
        PeriodicLattice.complexLieAlgebra := fun I hI => (hA.1 I hI).2
  exact ⟨fun 𝔇 m hm U hU => mapDerivAlongCurves_real hL hfp hleft hlr hv₂ ho₂ hm hU,
    fun 𝔇 F hF U hU => fnDerivAlongCurves_real hL hfp hleft hlr hv₁ ho₁ hF hU,
    fun β 𝔇 m hm U hU => mapDerivAlongCurves_holomorphic hh hel hlc hA.2.1 hv₄ ho₄ β hm hU,
    fun β 𝔇 F hF U hU => fnDerivAlongCurves_holomorphic hh hel hlc hv₃ ho₃ β hF hU⟩
end Tower.FullSpaceCurveDifferentials
end YangMills.Construction
end
