import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.Lattice.QuotientLatticesAndNeighbours
import YangMills.Construction.Matrices.ExpChartHolomorphy
import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.Matrices.FiniteMatrixProducts
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.CurvesAtAFiniteSideInTheLeftChart
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.CurveDifferentialsProof
open Matrices Coordinates Tower.LeftChartFields Tower.LeftChartFacts
section Submanifold
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
def chartOfStraightening {M : Set E} {l l' : ℕ}
    (q : OpenPartialHomeomorph E ((Fin l → ℝ) × (Fin l' → ℝ)))
    (hq : ContDiffOn ℝ ∞ q q.source) (hs : ContDiffOn ℝ ∞ q.symm q.target)
    (hM : q '' (q.source ∩ M) = q.target ∩ {z | z.2 = 0}) : EmbeddedSubmanifold.Chart M where
  dim := l
  source := {u | (u, (0 : Fin l' → ℝ)) ∈ q.target}
  param := fun u => q.symm (u, 0)
  isOpen_source := q.open_target.preimage (by fun_prop)
  contDiffOn_param :=
    hs.comp (contDiff_prodMk_left (0 : Fin l' → ℝ)).contDiffOn (fun _ hu => hu)
  injective_fderiv_param := by
    intro u hu
    have hu' : (u, (0 : Fin l' → ℝ)) ∈ q.target := hu
    have hsd : HasFDerivAt q.symm (fderiv ℝ q.symm (u, 0)) (u, (0 : Fin l' → ℝ)) :=
      ((hs.differentiableOn (by simp)) _ hu').differentiableAt
        (q.open_target.mem_nhds hu') |>.hasFDerivAt
    have hx : q.symm (u, 0) ∈ q.source := q.map_target hu'
    have hqd : HasFDerivAt q (fderiv ℝ q (q.symm (u, 0))) (q.symm (u, 0)) :=
      ((hq.differentiableOn (by simp)) _ hx).differentiableAt
        (q.open_source.mem_nhds hx) |>.hasFDerivAt
    have hcomp := hqd.comp (u, (0 : Fin l' → ℝ)) hsd
    have hid : HasFDerivAt (q ∘ q.symm) (ContinuousLinearMap.id ℝ _) (u, (0 : Fin l' → ℝ)) :=
      (hasFDerivAt_id _).congr_of_eventuallyEq
        (Filter.Eventually.mono (q.open_target.mem_nhds hu') fun y hy => q.right_inv hy)
    have heq := hcomp.unique hid
    have hp : HasFDerivAt (fun u' => q.symm (u', (0 : Fin l' → ℝ)))
        ((fderiv ℝ q.symm (u, 0)).comp (ContinuousLinearMap.inl ℝ _ _)) u :=
      HasFDerivAt.comp u hsd (hasFDerivAt_prodMk_left u 0)
    rw [hp.fderiv]
    intro w w' hww
    have h1 := congrArg (fderiv ℝ q (q.symm (u, 0))) hww
    have h2 : ∀ z, (fderiv ℝ q (q.symm (u, 0))) (fderiv ℝ q.symm (u, 0) z) = z := fun z =>
      DFunLike.congr_fun heq z
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, h2] at h1
    exact congrArg Prod.fst h1
  injOn_param := by
    intro u hu u' hu' h
    have h' : q (q.symm (u, (0 : Fin l' → ℝ))) = q (q.symm (u', (0 : Fin l' → ℝ))) :=
      congrArg q h
    rw [q.right_inv hu, q.right_inv hu'] at h'
    exact congrArg Prod.fst h'
  isRelativelyOpen_image := by
    intro W hWd hWo
    refine ⟨q.source ∩ q ⁻¹' (W ×ˢ univ), q.isOpen_inter_preimage (hWo.prod isOpen_univ), ?_⟩
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hud : (u, (0 : Fin l' → ℝ)) ∈ q.target := hWd hu
      have hin : (u, (0 : Fin l' → ℝ)) ∈ q '' (q.source ∩ M) := by
        rw [hM]
        exact ⟨hud, rfl⟩
      obtain ⟨y, ⟨hy, hyM⟩, hye⟩ := hin
      have hyx : q.symm (u, 0) = y := by rw [← hye, q.left_inv hy]
      refine ⟨⟨q.map_target hud, ?_⟩, ?_⟩
      · change q (q.symm (u, 0)) ∈ W ×ˢ univ
        rw [q.right_inv hud]
        exact ⟨hu, mem_univ _⟩
      · change q.symm (u, 0) ∈ M
        rw [hyx]
        exact hyM
    · rintro ⟨⟨hx, hxW⟩, hxM⟩
      have h2 : q x ∈ q.target ∩ {z | z.2 = 0} := by
        rw [← hM]
        exact ⟨x, ⟨hx, hxM⟩, rfl⟩
      refine ⟨(q x).1, hxW.1, ?_⟩
      have h3 : ((q x).1, (0 : Fin l' → ℝ)) = q x := Prod.ext rfl h2.2.symm
      change q.symm ((q x).1, 0) = x
      rw [h3, q.left_inv hx]
theorem exists_hasDerivAt_comp_curve {M O : Set E} (hM : Submanifolds.IsSmoothSubmanifold M)
    {f : E → F} (hf : EmbeddedSubmanifold.DifferentiableOnOpen M O f) {p : E} (hp : p ∈ O) :
    ∃ A : E →L[ℝ] F, ∀ (c : ℝ → E) (v : E), HasDerivAt c v 0 → c 0 = p →
      (∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ M) → HasDerivAt (fun t => f (c t)) (A v) 0 := by
  obtain ⟨⟨V, hVo, hOV⟩, hdiff⟩ := hf
  have hpM : p ∈ M := by
    rw [hOV] at hp
    exact hp.2
  obtain ⟨l, l', q, hpq, hq, hs, hqM⟩ := hM p hpM
  let c₀ : EmbeddedSubmanifold.Chart M := chartOfStraightening q hq hs hqM
  have hpar : ∀ x ∈ q.source ∩ M,
      q.symm ((q x).1, 0) = x ∧ ((q x).1, (0 : Fin l' → ℝ)) ∈ q.target := by
    intro x hx
    have h2 : q x ∈ q.target ∩ {z | z.2 = 0} := by
      rw [← hqM]
      exact ⟨x, hx, rfl⟩
    have h3 : ((q x).1, (0 : Fin l' → ℝ)) = q x := Prod.ext rfl h2.2.symm
    rw [h3]
    exact ⟨q.left_inv hx.1, h2.1⟩
  let u₀ : Fin l → ℝ := (q p).1
  have hu₀ : u₀ ∈ c₀.source := (hpar p ⟨hpq, hpM⟩).2
  have hu₀p : c₀.param u₀ = p := (hpar p ⟨hpq, hpM⟩).1
  have hparM : ∀ u ∈ c₀.source, c₀.param u ∈ M := by
    intro u hu
    obtain ⟨S, -, hS⟩ := c₀.isRelativelyOpen_image {u' | u' ∈ c₀.source} subset_rfl c₀.isOpen_source
    have : c₀.param u ∈ c₀.param '' {u' | u' ∈ c₀.source} := ⟨u, hu, rfl⟩
    rw [hS] at this
    exact this.2
  have hco : c₀.coords O = c₀.source ∩ c₀.param ⁻¹' V := by
    ext u
    constructor
    · rintro ⟨hu, huO⟩
      have huO' : c₀.param u ∈ O := huO
      rw [hOV] at huO'
      exact ⟨hu, huO'.1⟩
    · rintro ⟨hu, huV⟩
      refine ⟨hu, ?_⟩
      change c₀.param u ∈ O
      rw [hOV]
      exact ⟨huV, hparM u hu⟩
  have hcoOpen : IsOpen (c₀.coords O) := by
    rw [hco]
    exact c₀.contDiffOn_param.continuousOn.isOpen_inter_preimage c₀.isOpen_source hVo
  have hu₀O : u₀ ∈ c₀.coords O := ⟨hu₀, by
    change c₀.param u₀ ∈ O
    rw [hu₀p]
    exact hp⟩
  have hgd : DifferentiableAt ℝ (c₀.pullback f) u₀ :=
    (hdiff c₀ u₀ hu₀O).differentiableAt (hcoOpen.mem_nhds hu₀O)
  have hqd : HasFDerivAt q (fderiv ℝ q p) p :=
    ((hq.differentiableOn (by simp)) _ hpq).differentiableAt
      (q.open_source.mem_nhds hpq) |>.hasFDerivAt
  let π : E →L[ℝ] (Fin l → ℝ) := (ContinuousLinearMap.fst ℝ _ _).comp (fderiv ℝ q p)
  have hπ : HasFDerivAt (fun x => (q x).1) π p := hqd.fst
  refine ⟨(fderiv ℝ (c₀.pullback f) u₀).comp π, ?_⟩
  intro c v hc hc0 hcM
  have hcu : HasDerivAt (fun t => (q (c t)).1) (π v) 0 := by
    have hπ' : HasFDerivAt (fun x => (q x).1) π (c 0) := by rw [hc0]; exact hπ
    exact hπ'.comp_hasDerivAt 0 hc
  have hg' : HasFDerivAt (c₀.pullback f) (fderiv ℝ (c₀.pullback f) u₀) ((q (c 0)).1) := by
    rw [hc0]
    exact hgd.hasFDerivAt
  have hcomp := hg'.comp_hasDerivAt 0 hcu
  refine hcomp.congr_of_eventuallyEq ?_
  have hcs : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ q.source :=
    hc.continuousAt (q.open_source.mem_nhds (by rw [hc0]; exact hpq))
  filter_upwards [hcs, hcM] with t ht htM
  have h := (hpar (c t) ⟨ht, htM⟩).1
  change f (c t) = f (q.symm ((q (c t)).1, 0))
  rw [h]
end Submanifold
section Lattice
variable {L n k j : ℕ}
theorem isPos_or_opposite_isPos (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, h | h⟩ := b.isNeighbour
  · exact Or.inl ⟨μ, h⟩
  · refine Or.inr ⟨μ, ?_⟩
    change b.source - b.target = _
    rw [← neg_sub, h, neg_neg]
theorem not_isPos_opposite (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (b : Edge L n k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, hμ⟩ := hb
  rintro ⟨ν, hν⟩
  have hN := (hA L hL n j k hn hj).2.2.2.2.2.1
  have hs : QuotientLattices.IsSignedAxisStep
      (QuotientLattices.torusAxisSteps L n k j)
      (b.source : PeriodicLattice.FourTorus L n) (b.target : PeriodicLattice.FourTorus L n) 1 μ := by
    have h := congrArg Subtype.val hμ
    simpa [QuotientLattices.IsSignedAxisStep,
      QuotientLattices.torusAxisSteps] using h
  have hs' : QuotientLattices.IsSignedAxisStep
      (QuotientLattices.torusAxisSteps L n k j)
      (b.target : PeriodicLattice.FourTorus L n) (b.source : PeriodicLattice.FourTorus L n) 1 ν := by
    have h := congrArg Subtype.val hν
    simpa [QuotientLattices.IsSignedAxisStep,
      QuotientLattices.torusAxisSteps, PeriodicLattice.Bond.opposite] using h
  have hX := ((hN.2.2 _ b.source.2 _ b.target.2).2 1 μ hs).2
  rcases hX with ⟨-, h⟩ | ⟨-, h⟩
  · exact h ⟨ν, hs'⟩
  · exact h ⟨μ, hs⟩
theorem opposite_opposite (b : Edge L n k j) : b.opposite.opposite = b :=
  PeriodicLattice.Bond.ext rfl rfl
theorem nonempty_positiveEdge : Nonempty (PositiveEdge L n k j) := by
  rcases isPos_or_opposite_isPos (PeriodicLattice.Bond.forwardFrom (0 : Vertex L n k j) 0) with h | h
  · exact ⟨⟨_, h⟩⟩
  · exact ⟨⟨_, h⟩⟩
theorem extendOddly_congr {f g : Edge L n k j → ComplexMatrix2}
    (h : ∀ b, b.IsPositivelyOriented → f b = g b) :
    extendOddly f = extendOddly g := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [extendOddly, if_pos hb, h b hb]
  · simp only [extendOddly, if_neg hb, h _ ((isPos_or_opposite_isPos b).resolve_left hb)]
theorem isBondForm_extendOddly (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {𝔥 : Set ComplexMatrix2} {f : Edge L n k j → ComplexMatrix2}
    (h : ∀ b, b.IsPositivelyOriented → f b ∈ 𝔥) :
    PeriodicLattice.IsBondForm 𝔥 (extendOddly f) := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · simp only [extendOddly, if_pos hb]
    exact h b hb
  · by_cases hb : b.IsPositivelyOriented
    · have h' := not_isPos_opposite hA hL hn hj b hb
      simp only [extendOddly, if_neg h', if_pos hb, opposite_opposite]
    · have h' := (isPos_or_opposite_isPos b).resolve_left hb
      simp only [extendOddly, if_neg hb, if_pos h', neg_neg]
theorem fieldOfPositiveValues_restrict {U : Edge L n k j → ComplexMatrix2}
    (hrev : ∀ b : Edge L n k j, U b.opposite = (U b)⁻¹) :
    fieldOfPositiveValues (restrictToPositiveEdges U) = U := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [fieldOfPositiveValues, dif_pos hb, restrictToPositiveEdges]
  · have h' := (isPos_or_opposite_isPos b).resolve_left hb
    simp only [fieldOfPositiveValues, dif_neg hb, dif_pos h', restrictToPositiveEdges]
    rw [← hrev b.opposite, opposite_opposite]
theorem fieldOfPositiveValues_restrict_expTwist (X U : Edge L n k j → ComplexMatrix2) :
    fieldOfPositiveValues (restrictToPositiveEdges (PeriodicLattice.expTwist X U)) =
      PeriodicLattice.expTwist X U := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [fieldOfPositiveValues, dif_pos hb, restrictToPositiveEdges]
  · have h' := (isPos_or_opposite_isPos b).resolve_left hb
    simp only [fieldOfPositiveValues, dif_neg hb, dif_pos h', restrictToPositiveEdges,
      PeriodicLattice.expTwist, if_pos h', if_neg hb]
theorem expTwist_zero {U : Edge L n k j → ComplexMatrix2}
    (hrev : ∀ b : Edge L n k j, U b.opposite = (U b)⁻¹) :
    PeriodicLattice.expTwist (0 : Edge L n k j → ComplexMatrix2) U = U := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp [PeriodicLattice.expTwist, hb]
  · have h' := (isPos_or_opposite_isPos b).resolve_left hb
    have hb2 := hrev b.opposite
    rw [opposite_opposite] at hb2
    simp only [PeriodicLattice.expTwist, if_neg hb]
    rw [hb2]
    simp
theorem restrict_expTwist_smul (c : ℂ) (B U : Edge L n k j → ComplexMatrix2)
    (b : PositiveEdge L n k j) :
    restrictToPositiveEdges (PeriodicLattice.expTwist (c • B) U) b = leftExpMul (c • B b) (U b) := by
  simp only [restrictToPositiveEdges, PeriodicLattice.expTwist, if_pos b.2, leftExpMul,
    Pi.smul_apply]
theorem curveTangent_apply (γ : ℝ → Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    curveTangent γ b = Complex.I⁻¹ • (deriv (fun t => γ t b) 0 * (γ 0 b)⁻¹) := by
  simp only [curveTangent, extendOddly, if_pos hb]
theorem eventually_expTwist_mem {T : Type} [TopologicalSpace T] {t₀ : T}
    {𝒢 : Set ComplexMatrix2} {𝔇 : Set (Edge L n k j → ComplexMatrix2)} (hO : IsOpenFieldSet 𝒢 𝔇)
    {U : Edge L n k j → ComplexMatrix2} (hU : U ∈ 𝔇) {X : T → Edge L n k j → ComplexMatrix2}
    (hg : ∀ t, restrictToPositiveEdges (PeriodicLattice.expTwist (X t) U) ∈ edgePower L n k j 𝒢)
    (hc : ContinuousAt (fun t => restrictToPositiveEdges (PeriodicLattice.expTwist (X t) U)) t₀)
    (h0 : restrictToPositiveEdges (PeriodicLattice.expTwist (X t₀) U) = restrictToPositiveEdges U) :
    ∀ᶠ t in 𝓝 t₀, PeriodicLattice.expTwist (X t) U ∈ 𝔇 := by
  obtain ⟨S, hS, hSe⟩ := hO.2
  have hmem : restrictToPositiveEdges U ∈ S := by
    have h : restrictToPositiveEdges U ∈ restrictToPositiveEdges '' 𝔇 := ⟨U, hU, rfl⟩
    rw [hSe] at h
    exact h.1
  have hev : ∀ᶠ t in 𝓝 t₀, restrictToPositiveEdges (PeriodicLattice.expTwist (X t) U) ∈ S :=
    hc (hS.mem_nhds (by
      change restrictToPositiveEdges (PeriodicLattice.expTwist (X t₀) U) ∈ S
      rw [h0]
      exact hmem))
  filter_upwards [hev] with t ht
  have h : restrictToPositiveEdges (PeriodicLattice.expTwist (X t) U) ∈
      restrictToPositiveEdges '' 𝔇 := by
    rw [hSe]
    exact ⟨ht, hg t⟩
  obtain ⟨V, hV, hVe⟩ := h
  have hVc : PeriodicLattice.IsGaugeField 𝒢 univ V := hO.1 hV
  have hVX : V = PeriodicLattice.expTwist (X t) U := by
    rw [← fieldOfPositiveValues_restrict fun b => hVc.2 b (mem_univ b), hVe,
      fieldOfPositiveValues_restrict_expTwist]
  rw [← hVX]
  exact hV
end Lattice
theorem smul_deriv_logSeries (𝕜 : Type) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 ComplexMatrix2]
    {𝒢 𝔥 : Set ComplexMatrix2}
    (hlogs : ∀ ρ : ℝ, 0 < ρ → CurveLogDerivative 𝕜 (Metric.ball 0 ρ) 𝒢 𝔥)
    {W : 𝕜 → ComplexMatrix2} {d : ComplexMatrix2}
    (hW : HasDerivAt W d 0) (hev : ∀ᶠ t in 𝓝 (0 : 𝕜), W t ∈ 𝒢) :
    Complex.I⁻¹ • deriv (fun t => ComplexMatrix2.logSeries (W t * (W 0)⁻¹)) 0 =
      Complex.I⁻¹ • (d * (W 0)⁻¹) := by
  obtain ⟨ρ, hρ, hb⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have h := (hlogs ρ hρ W (fun t ht => hb t ht) hW.differentiableAt).2.2.1
  rwa [hW.deriv] at h
theorem ball_isOpenIntervalAroundZero {ρ : ℝ} (hρ : 0 < ρ) :
    IsOpenIntervalAroundZero (Metric.ball (0 : ℝ) ρ) :=
  ⟨Metric.isOpen_ball, (convex_ball (0 : ℝ) ρ).ordConnected, Metric.mem_ball_self hρ⟩
theorem curveTangent_eq_extendOddly {L n k j j' : ℕ}
    {m : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    {γ : ℝ → Edge L n k j → ComplexMatrix2} {g : Edge L n k j' → ComplexMatrix2}
    (hd : ∀ c : Edge L n k j', c.IsPositivelyOriented → ∃ d : ComplexMatrix2,
      HasDerivAt (fun t : ℝ => m (γ t) c) d 0 ∧ g c = Complex.I⁻¹ • (d * (m (γ 0) c)⁻¹)) :
    curveTangent (fun t => m (γ t)) = extendOddly g := by
  refine extendOddly_congr fun c hc => ?_
  obtain ⟨d, h1, h2⟩ := hd c hc
  rw [h1.deriv, h2]
def SmulCompatible (𝕜 V : Type) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℂ V] : Prop :=
  ∀ (c : 𝕜) (x : V), c • x = algebraMap 𝕜 ℂ c • x
theorem hasDerivAt_clm_comp {𝕜 V V' : Type} [NontriviallyNormedField 𝕜]
    [NormedAlgebra 𝕜 ℂ] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℂ V]
    [NormedAddCommGroup V'] [NormedSpace 𝕜 V'] [NormedSpace ℂ V']
    (h1 : SmulCompatible 𝕜 V) (h2 : SmulCompatible 𝕜 V') (φ : V →L[ℂ] V')
    {Y : 𝕜 → V} {Y' : V} (h : HasDerivAt Y Y' 0) : HasDerivAt (fun t => φ (Y t)) (φ Y') 0 := by
  let φ' : V →L[𝕜] V' :=
    ⟨{ toFun := φ
       map_add' := map_add φ
       map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        rw [h1, h2, map_smul] }, φ.continuous⟩
  exact φ'.hasFDerivAt.comp_hasDerivAt (0 : 𝕜) h
section Holomorphic
open GroupLieProduct
attribute [-instance] Matrix.module in
theorem exists_hasDerivAt_holomorphic_comp (hel : ComplexMatrix2.ExpLogEstimates)
    (hh : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {σ E' : Type} [Fintype σ] {l : ℕ} (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : E' ≃ ComplexCoordinates l) {W : Set (σ ⊕ Empty → ComplexMatrix2)}
    {Φ : (σ ⊕ Empty → ComplexMatrix2) → E'}
    (hΦ : IsHolomorphicToCoords β e W Φ) {p₀ : σ → ComplexMatrix2} (hp : asGroupFactors p₀ ∈ W)
    (hdet : ∀ s, (p₀ s).det = 1) :
    ∃ A : (σ → ComplexMatrix2) → ComplexCoordinates l, ∀ (𝕜 : Type) [NontriviallyNormedField 𝕜]
      [NormedAlgebra 𝕜 ℂ] [NormedSpace 𝕜 ComplexMatrix2],
      SmulCompatible 𝕜 ComplexMatrix2 →
      (∀ ρ : ℝ, 0 < ρ → CurveLogDerivative 𝕜 (Metric.ball 0 ρ)
        PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra) →
      ∀ (c : 𝕜 → σ → ComplexMatrix2) (v : σ → ComplexMatrix2),
        (∀ s, HasDerivAt (fun t => c t s) (v s) 0) →
        c 0 = p₀ → (∀ᶠ t in 𝓝 (0 : 𝕜), ∀ s, c t s ∈ PeriodicLattice.complexGaugeGroup) →
        HasDerivAt (fun t => e (Φ (asGroupFactors (c t)))) (A fun s => v s * (p₀ s)⁻¹) 0 := by
  classical
  obtain ⟨-, -, hpts⟩ := hΦ
  obtain ⟨O', h0, hW, -, hH⟩ := hpts (asGroupFactors p₀) hp
  let ν : (σ ⊕ Empty) ≃ Fin (Fintype.card (σ ⊕ Empty)) := Fintype.equivFin _
  let T := tupleOfCoords β ν
  have hT0 : T 0 = 0 := by
    funext i
    simp [T, tupleOfCoords, ComplexCoordinates.tracelessTuple]
  have hH' := hH ν
  have hΩ := hH'.1
  have h0Ω : (0 : ComplexCoordinates (Fintype.card (σ ⊕ Empty) * 3)) ∈
      tupleOfCoords β ν ⁻¹' O' := by
    change T 0 ∈ O'
    rw [hT0]
    exact h0
  obtain ⟨Lc, hL⟩ := ((hh.1 _ _ hΩ).1 _ _ hH').2.2.1 0 h0Ω
  have hL' := hasFDerivAt_of_restrictScalars ℝ hL rfl
  obtain ⟨r, hr⟩ :=
    (ComplexMatrix2.traceless.subtype).exists_leftInverse_of_injective (Submodule.ker_subtype _)
  let coef : Fin 3 → ComplexMatrix2 →L[ℂ] ℂ := fun a =>
    LinearMap.toContinuousLinearMap ((β.coord a).comp r)
  let extd : (σ → ComplexMatrix2) → σ ⊕ Empty → ComplexMatrix2 := fun Z => Sum.elim Z fun x => x.elim
  let wlin : (σ → ComplexMatrix2) → ComplexCoordinates (Fintype.card (σ ⊕ Empty) * 3) := fun Z k =>
    coef (finProdFinEquiv.symm k).2 (extd Z (ν.symm (finProdFinEquiv.symm k).1))
  have hTw : ∀ Z : σ → ComplexMatrix2, (∀ s, Z s ∈ ComplexMatrix2.traceless) →
      ∀ s, T (wlin Z) (.inl s) = Z s := by
    intro Z hZ s
    have hrz : r (Z s) = ⟨Z s, hZ s⟩ := LinearMap.congr_fun hr ⟨Z s, hZ s⟩
    have hk : ∀ a, wlin Z (finProdFinEquiv (ν (.inl s), a)) = β.repr ⟨Z s, hZ s⟩ a := by
      intro a
      have e1 : finProdFinEquiv.symm (finProdFinEquiv (ν (.inl s), a)) = (ν (.inl s), a) :=
        Equiv.symm_apply_apply _ _
      change coef (finProdFinEquiv.symm (finProdFinEquiv (ν (.inl s), a))).2
        (extd Z (ν.symm (finProdFinEquiv.symm (finProdFinEquiv (ν (.inl s), a))).1)) = _
      rw [e1]
      simp only [Equiv.symm_apply_apply]
      change β.coord a (r (Z s)) = _
      rw [hrz]
      rfl
    have h := congrArg (Subtype.val : ComplexMatrix2.traceless → ComplexMatrix2)
      (β.sum_repr ⟨Z s, hZ s⟩)
    rw [Submodule.coe_sum] at h
    calc T (wlin Z) (.inl s)
        = ∑ a, wlin Z (finProdFinEquiv (ν (.inl s), a)) • (β a : ComplexMatrix2) := rfl
      _ = ∑ a, β.repr ⟨Z s, hZ s⟩ a • (β a : ComplexMatrix2) :=
          Finset.sum_congr rfl fun a _ => by rw [hk a]
      _ = Z s := h
  refine ⟨fun Z => Lc (wlin Z), ?_⟩
  intro 𝕜 _ _ _ hsm hlogs c v hc hc0 hcg
  let Y : 𝕜 → σ → ComplexMatrix2 := fun t s => ComplexMatrix2.logSeries (c t s * (p₀ s)⁻¹)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hcg
  have hunit : ∀ s, IsUnit (p₀ s).det := fun s => by rw [hdet s]; exact isUnit_one
  have hYd : ∀ s, HasDerivAt (fun t => Y t s) (v s * (p₀ s)⁻¹) 0 := by
    intro s
    have h := hlogs ρ hρ (fun t => c t s) (fun t ht => hball t ht s) (hc s).differentiableAt
    have hd := h.2.1.hasDerivAt
    have he := h.2.2.1
    rw [(hc s).deriv] at he
    have hc0s : c 0 s = p₀ s := congrFun hc0 s
    simp only [hc0s] at he hd
    have he' := smul_right_injective ComplexMatrix2 (inv_ne_zero Complex.I_ne_zero) he
    rw [he'] at hd
    exact hd
  have hnear : ∀ᶠ t in 𝓝 (0 : 𝕜), ∀ s, ‖c t s * (p₀ s)⁻¹ - 1‖ ≤ 9 / 10 := by
    rw [Filter.eventually_all]
    intro s
    have hcs : ContinuousAt (fun t => ‖c t s * (p₀ s)⁻¹ - 1‖) 0 :=
      (((hc s).continuousAt.mul continuousAt_const).sub continuousAt_const).norm
    have hz : ‖c 0 s * (p₀ s)⁻¹ - 1‖ = 0 := by
      rw [congrFun hc0 s, Matrix.mul_nonsing_inv _ (hunit s), sub_self, norm_zero]
    have := hcs.eventually (gt_mem_nhds (show ‖c 0 s * (p₀ s)⁻¹ - 1‖ < 9 / 10 by
      rw [hz]; norm_num))
    exact this.mono fun t ht => le_of_lt ht
  have hid : ∀ᶠ t in 𝓝 (0 : 𝕜), ∀ s,
      Y t s ∈ ComplexMatrix2.traceless ∧ ComplexMatrix2.matExp (Y t s) * p₀ s = c t s := by
    filter_upwards [hnear, hcg] with t ht htg s
    have hdetX : (c t s * (p₀ s)⁻¹).det = 1 := by
      have h1 : (c t s).det = 1 := htg s
      rw [Matrix.det_mul, h1, Matrix.det_nonsing_inv, hdet s]
      simp
    refine ⟨(hel.2.2.2.2.2.2.1 _ hdetX (ht s)).2, ?_⟩
    have hlt : ‖c t s * (p₀ s)⁻¹ - 1‖ < 1 := lt_of_le_of_lt (ht s) (by norm_num)
    have hex := (hel.2.2.2.1 _ hlt).2.2.2.2
    rw [add_sub_cancel] at hex
    change ComplexMatrix2.matExp (ComplexMatrix2.logSeries (c t s * (p₀ s)⁻¹)) * p₀ s = c t s
    rw [hex, mul_assoc, Matrix.nonsing_inv_mul _ (hunit s), mul_one]
  have hw : HasDerivAt (fun t => wlin (Y t)) (wlin fun s => v s * (p₀ s)⁻¹) 0 := by
    refine hasDerivAt_pi.2 fun k => ?_
    rcases hk : ν.symm (finProdFinEquiv.symm k).1 with s | x
    · have h := hasDerivAt_clm_comp hsm (fun a x => (algebraMap_smul ℂ a x).symm)
        (coef (finProdFinEquiv.symm k).2) (hYd s)
      simpa only [wlin, extd, hk, Sum.elim_inl] using h
    · exact x.elim
  have hw0 : wlin (Y 0) = 0 := by
    funext k
    have hY0 : ∀ s, Y 0 s = 0 := by
      intro s
      change ComplexMatrix2.logSeries (c 0 s * (p₀ s)⁻¹) = 0
      rw [congrFun hc0 s, Matrix.mul_nonsing_inv _ (hunit s)]
      simp [ComplexMatrix2.logSeries]
    change coef (finProdFinEquiv.symm k).2 (extd (Y 0) (ν.symm (finProdFinEquiv.symm k).1)) = 0
    rcases ν.symm (finProdFinEquiv.symm k).1 with s | x
    · simp only [extd, Sum.elim_inl, hY0, map_zero]
    · exact x.elim
  have hat : HasFDerivAt (e ∘ (Φ ∘ expChartAt (asGroupFactors p₀)) ∘ T)
      (Lc.restrictScalars 𝕜) (wlin (Y 0)) := by
    rw [hw0]
    exact hL'.restrictScalars 𝕜
  have hcomp := hat.comp_hasDerivAt (0 : 𝕜) hw
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hid] with t ht
  have hch : expChartAt (asGroupFactors p₀) (T (wlin (Y t))) = asGroupFactors (c t) := by
    funext x
    rcases x with s | x
    · change ComplexMatrix2.matExp (T (wlin (Y t)) (.inl s)) * p₀ s = c t s
      rw [hTw (Y t) (fun s => (ht s).1) s]
      exact (ht s).2
    · exact x.elim
  change e (Φ (asGroupFactors (c t))) = e (Φ (expChartAt (asGroupFactors p₀) (T (wlin (Y t)))))
  rw [hch]
attribute [-instance] Matrix.module in
theorem hasDerivAt_of_hasDerivAt_matrixEquiv (𝕜 : Type) [NontriviallyNormedField 𝕜]
    [NormedAlgebra 𝕜 ℂ] [NormedSpace 𝕜 ComplexMatrix2] (hsm : SmulCompatible 𝕜 ComplexMatrix2)
    {f : 𝕜 → ComplexMatrix2} {d : ComplexCoordinates 4}
    (h : HasDerivAt (fun t => ComplexCoordinates.matrixEquiv (f t)) d 0) :
    HasDerivAt f (ComplexCoordinates.matrixEquiv.symm d) 0 := by
  let Ce : ComplexCoordinates 4 →ₗ[ℂ] ComplexMatrix2 :=
    { toFun := ComplexCoordinates.matrixEquiv.symm
      map_add' := fun x y => by
        ext i i'
        simp [ComplexCoordinates.matrixEquiv]
      map_smul' := fun a x => by
        ext i i'
        simp [ComplexCoordinates.matrixEquiv] }
  let Cc : ComplexCoordinates 4 →L[ℂ] ComplexMatrix2 := LinearMap.toContinuousLinearMap Ce
  have h1 := hasDerivAt_clm_comp (fun a x => (algebraMap_smul ℂ a x).symm) hsm Cc h
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  exact (ComplexCoordinates.matrixEquiv.symm_apply_apply (f t)).symm
end Holomorphic
section Curves
variable {L n k j j' : ℕ}
theorem I_smul_inv_smul_mul {D V : ComplexMatrix2} (hV : V.det = 1) :
    Complex.I • (Complex.I⁻¹ • (D * V⁻¹)) * V = D := by
  rw [smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul, mul_assoc,
    Matrix.nonsing_inv_mul _ (by rw [hV]; exact isUnit_one), mul_one]
theorem hasDerivAt_at_edge {𝒢 : Set ComplexMatrix2} {I : Set ℝ}
    {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (hγ : IsDifferentiableFieldCurve 𝒢 I γ) {b : Edge L n k j} (hb : b.IsPositivelyOriented) :
    HasDerivAt (fun t => γ t b) (deriv (fun t => γ t b) 0) 0 :=
  ((hγ.2.2 b hb).differentiableAt (hγ.1.1.mem_nhds hγ.1.2.2)).hasDerivAt
theorem isGaugeField_at {𝒢 : Set ComplexMatrix2} {I : Set ℝ}
    {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (hγ : IsDifferentiableFieldCurve 𝒢 I γ) {t : ℝ} (ht : t ∈ I) :
    PeriodicLattice.IsGaugeField 𝒢 univ (γ t) := hγ.2.1 ht
theorem eventually_mem_interval {𝒢 : Set ComplexMatrix2} {I : Set ℝ}
    {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (hγ : IsDifferentiableFieldCurve 𝒢 I γ) : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ I :=
  hγ.1.1.mem_nhds hγ.1.2.2
theorem fieldOfPositiveValues_restrict_at {𝒢 : Set ComplexMatrix2} {I : Set ℝ}
    {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (hγ : IsDifferentiableFieldCurve 𝒢 I γ) {t : ℝ} (ht : t ∈ I) :
    fieldOfPositiveValues (restrictToPositiveEdges (γ t)) = γ t :=
  fieldOfPositiveValues_restrict fun b => (isGaugeField_at hγ ht).2 b (mem_univ b)
theorem curveTangent_isBondForm (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {𝒢 𝔥 : Set ComplexMatrix2} {I : Set ℝ}
    {γ : ℝ → Edge L n k j → ComplexMatrix2} (hlog : CurveLogDerivative ℝ I 𝒢 𝔥)
    (hγ : IsDifferentiableFieldCurve 𝒢 I γ) : PeriodicLattice.IsBondForm 𝔥 (curveTangent γ) :=
  isBondForm_extendOddly hA hL hn hj fun b hb =>
    (hlog (fun t => γ t b) (fun _ ht => (isGaugeField_at hγ ht).1 b (mem_univ b))
      (hasDerivAt_at_edge hγ hb).differentiableAt).2.2.2
theorem expTwist_algebraMap_zero_smul (𝕜 : Type) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    {U B : Edge L n k j → ComplexMatrix2} (hrev : ∀ b : Edge L n k j, U b.opposite = (U b)⁻¹) :
    PeriodicLattice.expTwist (algebraMap 𝕜 ℂ 0 • B) U = U := by
  rw [map_zero, zero_smul, expTwist_zero hrev]
theorem real_exp_curve (hC : Tower.LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {U B : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.compactGaugeGroup) (hB : B ∈ edgeFormSpace L n k j) :
    (∀ t : ℝ, restrictToPositiveEdges (PeriodicLattice.expTwist (algebraMap ℝ ℂ t • B) U) ∈
      edgePower L n k j PeriodicLattice.compactGaugeGroup) ∧
    ∀ b : PositiveEdge L n k j,
      HasDerivAt (fun t : ℝ =>
          restrictToPositiveEdges (PeriodicLattice.expTwist (algebraMap ℝ ℂ t • B) U) b)
        (Complex.I • B b * U b) 0 := by
  have hleft := ((hC.2.2 L k j hL hj).1 n hn).1.1.1 U hU B hB
  refine ⟨fun t b => ?_, fun b => ?_⟩
  · rw [restrict_expTwist_smul]
    exact (hleft b).1 t
  · exact (hleft b).2.congr_of_eventuallyEq
      (Eventually.of_forall fun t => restrict_expTwist_smul _ _ _ _)
theorem complex_exp_curve (hC : Tower.LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    {U B : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms L n k j) :
    (∀ t : ℂ, restrictToPositiveEdges (PeriodicLattice.expTwist (algebraMap ℂ ℂ t • B) U) ∈
      edgePower L n k j PeriodicLattice.complexGaugeGroup) ∧
    ∀ b : PositiveEdge L n k j,
      HasDerivAt (fun t : ℂ =>
          restrictToPositiveEdges (PeriodicLattice.expTwist (algebraMap ℂ ℂ t • B) U) b)
        (Complex.I • B b * U b) 0 := by
  have hleft := ((hC.2.2 L k j hL hj).1 n hn).1.1.2 U hU B hB
  refine ⟨fun t b => ?_, fun b => ?_⟩
  · rw [restrict_expTwist_smul]
    exact (hleft b).1 t
  · exact (hleft b).2.congr_of_eventuallyEq
      (Eventually.of_forall fun t => restrict_expTwist_smul _ _ _ _)
theorem real_derivative_agrees {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (hC : Tower.LeftChartFields.Claim) (hE : FamilyProducts.FamilyProductsStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    [Fintype (PositiveEdge L n k j)] {I : Set ℝ} {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (hγ : IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup I γ)
    (hB : curveTangent γ ∈ edgeFormSpace L n k j)
    {O : Set (PositiveEdge L n k j → ComplexMatrix2)} {f : (PositiveEdge L n k j → ComplexMatrix2) → F'}
    (hf : EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower (PositiveEdge L n k j)) O f)
    (hU : restrictToPositiveEdges (γ 0) ∈ O) :
    ∃ d : F', HasDerivAt (fun t => f (restrictToPositiveEdges (γ t))) d 0 ∧
      HasDerivAt (fun t : ℝ => f (restrictToPositiveEdges
        (PeriodicLattice.expTwist (algebraMap ℝ ℂ t • curveTangent γ) (γ 0)))) d 0 := by
  have : Nonempty (PositiveEdge L n k j) := nonempty_positiveEdge
  obtain ⟨A, hAc⟩ := exists_hasDerivAt_comp_curve (hE (PositiveEdge L n k j)).2.2 hf hU
  have h0 := isGaugeField_at hγ hγ.1.2.2
  obtain ⟨hg, hd⟩ := real_exp_curve hC hL hn hj (U := γ 0) h0 hB
  have hv : ∀ b : PositiveEdge L n k j, Complex.I • curveTangent γ b * γ 0 b =
      deriv (fun t => γ t b) 0 := by
    intro b
    rw [curveTangent_apply γ b.2]
    exact I_smul_inv_smul_mul (Matrix.mem_specialUnitaryGroup_iff.1 (h0.1 b.1 (mem_univ _))).2
  refine ⟨A fun b => deriv (fun t => γ t b) 0,
    hAc _ _ (hasDerivAt_pi.2 fun b => hasDerivAt_at_edge hγ b.2) rfl ?_,
    hAc _ _ (hasDerivAt_pi.2 fun b => ?_) ?_ (Eventually.of_forall hg)⟩
  · filter_upwards [eventually_mem_interval hγ] with t ht
    exact fun b => (isGaugeField_at hγ ht).1 b.1 (mem_univ _)
  · rw [← hv b]
    exact hd b
  · rw [expTwist_algebraMap_zero_smul ℝ fun b => h0.2 b (mem_univ b)]
open GroupLieProduct in
theorem holomorphic_derivative_agrees {E' : Type} {l : ℕ}
    (hC : Tower.LeftChartFields.Claim)
    (hel : ComplexMatrix2.ExpLogEstimates)
    (hh : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    [Fintype (PositiveEdge L n k j)] (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : E' ≃ ComplexCoordinates l) {I : Set ℝ} {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (hγ : IsDifferentiableFieldCurve PeriodicLattice.complexGaugeGroup I γ)
    (hB : curveTangent γ ∈ complexEdgeForms L n k j)
    {W : Set (PositiveEdge L n k j ⊕ Empty → ComplexMatrix2)}
    {Φ : (PositiveEdge L n k j ⊕ Empty → ComplexMatrix2) → E'}
    (hΦ : IsHolomorphicToCoords β e W Φ)
    (hU : asGroupFactors (restrictToPositiveEdges (γ 0)) ∈ W) :
    ∃ d : ComplexCoordinates l,
      HasDerivAt (fun t : ℝ => e (Φ (asGroupFactors (restrictToPositiveEdges (γ t))))) d 0 ∧
      HasDerivAt (fun t : ℂ => e (Φ (asGroupFactors (restrictToPositiveEdges
        (PeriodicLattice.expTwist (algebraMap ℂ ℂ t • curveTangent γ) (γ 0)))))) d 0 := by
  have h0 := isGaugeField_at hγ hγ.1.2.2
  have hdet : ∀ b : PositiveEdge L n k j, (restrictToPositiveEdges (γ 0) b).det = 1 :=
    fun b => h0.1 b.1 (mem_univ _)
  obtain ⟨A, hAc⟩ := exists_hasDerivAt_holomorphic_comp hel hh β e hΦ hU hdet
  obtain ⟨hg, hd⟩ := complex_exp_curve hC hL hn hj (U := γ 0) h0 hB
  have hlogsR : ∀ ρ : ℝ, 0 < ρ → CurveLogDerivative ℝ (Metric.ball 0 ρ)
      PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra :=
    fun ρ hρ => (hC.1 _ (ball_isOpenIntervalAroundZero hρ)).2
  have hv : ∀ b : PositiveEdge L n k j, Complex.I • curveTangent γ b * γ 0 b =
      deriv (fun t => γ t b) 0 := by
    intro b
    rw [curveTangent_apply γ b.2]
    exact I_smul_inv_smul_mul (hdet b)
  have h1 := hAc ℝ (fun a M => (Complex.coe_smul a M).symm) hlogsR
    (fun t => restrictToPositiveEdges (γ t))
    (fun b => deriv (fun t => γ t b) 0) (fun b => hasDerivAt_at_edge hγ b.2) rfl
    (by
      filter_upwards [eventually_mem_interval hγ] with t ht
      exact fun b => (isGaugeField_at hγ ht).1 b.1 (mem_univ _))
  have h2 := hAc ℂ (fun a M => rfl) hC.2.1
    (fun t => restrictToPositiveEdges
      (PeriodicLattice.expTwist (algebraMap ℂ ℂ t • curveTangent γ) (γ 0)))
    (fun b => deriv (fun t => γ t b) 0)
    (fun b => by rw [← hv b]; exact hd b)
    (by
      change restrictToPositiveEdges
        (PeriodicLattice.expTwist (algebraMap ℂ ℂ 0 • curveTangent γ) (γ 0)) = _
      rw [expTwist_algebraMap_zero_smul ℂ fun b => h0.2 b (mem_univ b)])
    (Eventually.of_forall fun t b => hg t b)
  exact ⟨_, h1, h2⟩
theorem differentialsFromCurves (hC : Tower.LeftChartFields.Claim)
    (hE : FamilyProducts.FamilyProductsStatement)
    (hH : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hel : ComplexMatrix2.ExpLogEstimates)
    (hh : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) :
    Tower.LeftChartFacts.DifferentialsFromCurves L n k j j' := by
  have hlogsR : ∀ ρ : ℝ, 0 < ρ → CurveLogDerivative ℝ (Metric.ball 0 ρ)
      PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra :=
    fun ρ hρ => (hC.1 _ (ball_isOpenIntervalAroundZero hρ)).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro 𝔇 m hm U hU I γ hγ h0
    subst h0
    obtain ⟨hO, hmap, inst₁, inst₂, hdiff⟩ := hm
    have hB : curveTangent γ ∈ edgeFormSpace L n k j :=
      curveTangent_isBondForm hA hL hn hj ((hC.1 I hγ.1).1) hγ
    have hkey : ∀ c : Edge L n k j', c.IsPositivelyOriented → ∃ d : ComplexMatrix2,
        HasDerivAt (fun t : ℝ => m (γ t) c) d 0 ∧
        HasDerivAt (fun t : ℝ => m (PeriodicLattice.expTwist
          (algebraMap ℝ ℂ t • curveTangent γ) (γ 0)) c) d 0 := by
      intro c hc
      obtain ⟨d, h1, h2⟩ := real_derivative_agrees hC hE hL hn hj hγ hB hdiff.1 ⟨_, hU, rfl⟩
      refine ⟨d ⟨c, hc⟩, (hasDerivAt_pi.1 h1 ⟨c, hc⟩).congr_of_eventuallyEq ?_,
        (hasDerivAt_pi.1 h2 ⟨c, hc⟩).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)⟩
      · filter_upwards [eventually_mem_interval hγ] with t ht
        change m (γ t) c = m (fieldOfPositiveValues (restrictToPositiveEdges (γ t))) c
        rw [fieldOfPositiveValues_restrict_at hγ ht]
      · change m _ c = m (fieldOfPositiveValues (restrictToPositiveEdges _)) c
        rw [fieldOfPositiveValues_restrict_expTwist]
    have h0c := isGaugeField_at hγ hγ.1.2.2
    obtain ⟨hg, hd⟩ := real_exp_curve hC hL hn hj (U := γ 0) h0c hB
    have hdom := eventually_expTwist_mem hO hU
      (X := fun t : ℝ => algebraMap ℝ ℂ t • curveTangent γ) hg
      (continuousAt_pi.2 fun b => (hd b).continuousAt)
      (by rw [expTwist_algebraMap_zero_smul ℝ fun b => h0c.2 b (mem_univ b)])
    have hz := expTwist_algebraMap_zero_smul ℝ (B := curveTangent γ)
      fun b => h0c.2 b (mem_univ b)
    refine ⟨fun c hc => (hkey c hc).choose_spec.1.differentiableAt, ?_⟩
    refine curveTangent_eq_extendOddly fun c hc => ?_
    obtain ⟨d, h1, h2⟩ := hkey c hc
    refine ⟨d, h1, ?_⟩
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), m (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ t • curveTangent γ) (γ 0)) c ∈ PeriodicLattice.compactGaugeGroup := by
      filter_upwards [hdom] with t ht
      exact (show PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup univ _ from
        hmap ht).1 c (mem_univ _)
    have h := smul_deriv_logSeries ℝ hlogsR h2 hev
    simp only [hz] at h
    exact h
  · intro 𝔇 F hF U hU I γ hγ h0
    subst h0
    obtain ⟨hO, inst, hf⟩ := hF
    have hB : curveTangent γ ∈ edgeFormSpace L n k j :=
      curveTangent_isBondForm hA hL hn hj ((hC.1 I hγ.1).1) hγ
    obtain ⟨d, h1, h2⟩ := real_derivative_agrees hC hE hL hn hj hγ hB hf ⟨_, hU, rfl⟩
    have e1 : HasDerivAt (fun t => F (γ t)) d 0 := by
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [eventually_mem_interval hγ] with t ht
      rw [fieldOfPositiveValues_restrict_at hγ ht]
    have e2 : HasDerivAt (fun t : ℝ => F (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ t • curveTangent γ) (γ 0))) d 0 := by
      refine h2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
      change F _ = F (fieldOfPositiveValues (restrictToPositiveEdges _))
      rw [fieldOfPositiveValues_restrict_expTwist]
    have e3 : leftDeriv F (γ 0) (curveTangent γ) = d := e2.deriv
    rw [e3]
    exact e1
  · intro β 𝔇 m hm U hU I γ hγ h0
    subst h0
    obtain ⟨hO, hmap, inst₁, inst₂, hhol⟩ := hm
    have hB : curveTangent γ ∈ complexEdgeForms L n k j :=
      curveTangent_isBondForm hA hL hn hj ((hC.1 I hγ.1).2) hγ
    have hkey : ∀ c : Edge L n k j', c.IsPositivelyOriented → ∃ d : ComplexMatrix2,
        HasDerivAt (fun t : ℝ => m (γ t) c) d 0 ∧
        HasDerivAt (fun t : ℂ => m (PeriodicLattice.expTwist
          (algebraMap ℂ ℂ t • curveTangent γ) (γ 0)) c) d 0 := by
      intro c hc
      have hi := hhol.2.1 ⟨c, hc⟩
      have hcoord := ((hH.2.2.2.1 (PositiveEdge L n k j) Empty).2.1 β _ _ hi.1 hi.2.1).1 hi
      obtain ⟨d, h1, h2⟩ := holomorphic_derivative_agrees hC hel hh hL hn hj β
        ComplexCoordinates.matrixEquiv hγ hB hcoord ⟨_, ⟨_, hU, rfl⟩, rfl⟩
      have h1' : HasDerivAt (fun t : ℝ => ComplexCoordinates.matrixEquiv
          (m (fieldOfPositiveValues (restrictToPositiveEdges (γ t))) c)) d 0 := h1
      have h2' : HasDerivAt (fun t : ℂ => ComplexCoordinates.matrixEquiv
          (m (fieldOfPositiveValues (restrictToPositiveEdges (PeriodicLattice.expTwist
            (algebraMap ℂ ℂ t • curveTangent γ) (γ 0)))) c)) d 0 := h2
      refine ⟨ComplexCoordinates.matrixEquiv.symm d,
        (hasDerivAt_of_hasDerivAt_matrixEquiv ℝ (fun a M => (Complex.coe_smul a M).symm)
          h1').congr_of_eventuallyEq ?_,
        (hasDerivAt_of_hasDerivAt_matrixEquiv ℂ (fun a M => rfl) h2').congr_of_eventuallyEq
          (Eventually.of_forall fun t => ?_)⟩
      · filter_upwards [eventually_mem_interval hγ] with t ht
        rw [fieldOfPositiveValues_restrict_at hγ ht]
      · change m _ c = m (fieldOfPositiveValues (restrictToPositiveEdges _)) c
        rw [fieldOfPositiveValues_restrict_expTwist]
    have h0c := isGaugeField_at hγ hγ.1.2.2
    obtain ⟨hg, hd⟩ := complex_exp_curve hC hL hn hj (U := γ 0) h0c hB
    have hdom := eventually_expTwist_mem hO hU
      (X := fun t : ℂ => algebraMap ℂ ℂ t • curveTangent γ) hg
      (continuousAt_pi.2 fun b => (hd b).continuousAt)
      (by rw [expTwist_algebraMap_zero_smul ℂ fun b => h0c.2 b (mem_univ b)])
    have hz := expTwist_algebraMap_zero_smul ℂ (B := curveTangent γ)
      fun b => h0c.2 b (mem_univ b)
    refine ⟨fun c hc => (hkey c hc).choose_spec.1.differentiableAt, ?_⟩
    refine curveTangent_eq_extendOddly fun c hc => ?_
    obtain ⟨d, h1, h2⟩ := hkey c hc
    refine ⟨d, h1, ?_⟩
    have hev : ∀ᶠ t in 𝓝 (0 : ℂ), m (PeriodicLattice.expTwist
        (algebraMap ℂ ℂ t • curveTangent γ) (γ 0)) c ∈ PeriodicLattice.complexGaugeGroup := by
      filter_upwards [hdom] with t ht
      exact (show PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ _ from
        hmap ht).1 c (mem_univ _)
    have h := smul_deriv_logSeries ℂ hC.2.1 h2 hev
    simp only [hz] at h
    exact h
  · intro β 𝔇 F hF U hU I γ hγ h0
    subst h0
    obtain ⟨hO, inst, hf⟩ := hF
    have hB : curveTangent γ ∈ complexEdgeForms L n k j :=
      curveTangent_isBondForm hA hL hn hj ((hC.1 I hγ.1).2) hγ
    obtain ⟨d, h1, h2⟩ := holomorphic_derivative_agrees hC hel hh hL hn hj β
      (Equiv.funUnique (Fin 1) ℂ).symm hγ hB hf ⟨_, ⟨_, hU, rfl⟩, rfl⟩
    have hz : ∀ x : ℂ, (Equiv.funUnique (Fin 1) ℂ).symm x 0 = x := fun x => by simp
    have e1 : HasDerivAt (fun t => F (γ t)) (d 0) 0 := by
      refine (hasDerivAt_pi.1 h1 0).congr_of_eventuallyEq ?_
      filter_upwards [eventually_mem_interval hγ] with t ht
      rw [hz]
      change F (γ t) = F (fieldOfPositiveValues (restrictToPositiveEdges (γ t)))
      rw [fieldOfPositiveValues_restrict_at hγ ht]
    have e2 : HasDerivAt (fun t : ℂ => F (PeriodicLattice.expTwist
        (algebraMap ℂ ℂ t • curveTangent γ) (γ 0))) (d 0) 0 := by
      have h2' : HasDerivAt (fun t : ℂ => (Equiv.funUnique (Fin 1) ℂ).symm
          (F (fieldOfPositiveValues (restrictToPositiveEdges (PeriodicLattice.expTwist
            (algebraMap ℂ ℂ t • curveTangent γ) (γ 0)))))) d 0 := h2
      have h3 := hasDerivAt_pi.1 h2' 0
      simp only [hz, fieldOfPositiveValues_restrict_expTwist] at h3
      exact h3
    have e3 : holLeftDeriv F (γ 0) (curveTangent γ) = d 0 := e2.deriv
    rw [e3]
    exact e1
end Curves
theorem finiteLevelCurveDifferentials (hC : Tower.LeftChartFields.Claim)
    (hE : FamilyProducts.FamilyProductsStatement)
    (hH : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hel : ComplexMatrix2.ExpLogEstimates)
    (hh : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties) :
    Tower.FiniteLevelCurveDifferentials.Statement :=
  fun _ _ _ _ hL hj _ _ hn => differentialsFromCurves hC hE hH hel hh hA hL hn hj
end YangMills.Construction.Tower.CurveDifferentialsProof
end
