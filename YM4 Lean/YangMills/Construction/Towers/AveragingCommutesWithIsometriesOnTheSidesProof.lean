import YangMills.Construction.Lattice.CovarianceOfTheAveragingMaps
import YangMills.Construction.Lattice.IsometryCovarianceOfHolonomiesAndActions
import YangMills.Construction.Lattice.LevelBondOrientationDichotomy
import YangMills.Construction.Towers.AveragingCommutesWithIsometriesOnTheSides
import YangMills.Construction.Towers.AveragingIsAnalyticAndCovariantOnTheSides
import YangMills.Construction.Towers.LatticesIsometriesDilationsAndQuotientsOfATower
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.EquivariantOnSides
variable {L n k i : ℕ}
theorem eq_of_restrictToPositiveEdges_eq
    (hX : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 0 < k) (hi : i ≤ k)
    {U U' : Edge L n k i → Matrices.ComplexMatrix2} (hU : U ∈ fieldSpace L n k i)
    (hU' : U' ∈ fieldSpace L n k i)
    (h : restrictToPositiveEdges U = restrictToPositiveEdges U') : U = U' := by
  funext e
  have he : e.IsPositivelyOriented ∨ e.opposite.IsPositivelyOriented := by
    rcases hX L n k hL hn hk i hi e with h' | h'
    · exact Or.inl h'.1
    · exact Or.inr h'.1
  rcases he with he | he
  · exact congrFun h ⟨e, he⟩
  · have h₁ : U e = (U e.opposite)⁻¹ := hU.2 e.opposite (mem_univ _)
    have h₂ : U' e = (U' e.opposite)⁻¹ := hU'.2 e.opposite (mem_univ _)
    have h₃ : U e.opposite = U' e.opposite := congrFun h ⟨e.opposite, he⟩
    rw [h₁, h₂, h₃]
theorem eventually_mem_of_isOpenNhdOfOne
    (hX : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 0 < k) (hi : i ≤ k)
    {W : Set (Edge L n k i → Matrices.ComplexMatrix2)} (h : IsOpenNhdOfOne W) :
    ∀ᶠ U in 𝓝[fieldSpace L n k i] trivialField L n k i, U ∈ W := by
  obtain ⟨⟨hsub, O, hO, himg⟩, h1⟩ := h
  have hcont : Continuous
      (restrictToPositiveEdges :
        (Edge L n k i → Matrices.ComplexMatrix2) → PositiveEdge L n k i → Matrices.ComplexMatrix2) :=
    continuous_pi fun _ => continuous_apply _
  have hpos1 : restrictToPositiveEdges (trivialField L n k i) ∈ O := by
    have : restrictToPositiveEdges (trivialField L n k i) ∈ restrictToPositiveEdges '' W :=
      mem_image_of_mem _ h1
    rw [himg] at this
    exact this.1
  have hOn : ∀ᶠ U in 𝓝 (trivialField L n k i), restrictToPositiveEdges U ∈ O :=
    hcont.continuousAt.eventually_mem (hO.mem_nhds hpos1)
  filter_upwards [nhdsWithin_le_nhds hOn, self_mem_nhdsWithin] with U h₁ h₂
  have hmem : restrictToPositiveEdges U ∈ restrictToPositiveEdges '' W := by
    rw [himg]
    exact ⟨h₁, fun e => h₂.1 _ (mem_univ _)⟩
  obtain ⟨U', hU', he⟩ := hmem
  have : U' = U := eq_of_restrictToPositiveEdges_eq hX hL hn hk hi (hsub hU') h₂ he
  exact this ▸ hU'
theorem exists_mem_latticeIsometries
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    {w : InfiniteLattice.AmbientSpace ≃ₗ[ℝ] InfiniteLattice.AmbientSpace}
    (hw : w ∈ InfiniteLattice.hyperoctahedralLinearGroup) {v : InfiniteLattice.AmbientSpace}
    (hv : v ∈ InfiniteLattice.latticeSubgroup (meshAt L k i))
    (hwv : ∀ x : InfiniteLattice.AmbientSpace,
      f (TorusMetric.torusProj (PeriodicLattice.torusSide L n) x) =
        TorusMetric.torusProj (PeriodicLattice.torusSide L n) (w x + v)) :
    ∃ σ : PeriodicLattice.FourTorus L n ≃ PeriodicLattice.FourTorus L n, (∀ x, σ x = f x) ∧
      σ ∈ PeriodicLattice.latticeIsometries L n (PeriodicLattice.levelDepth k i) := by
  obtain ⟨π, s, hπ⟩ := (InfiniteLattice.mem_hyperoctahedralLinearGroup_iff w).mp hw
  let r : PeriodicLattice.SignedFrame := (π, s)
  have hr : ∀ x : Fin 4 → ℝ, r.actOnVector x = w x := fun x => by
    funext μ
    simp [PeriodicLattice.SignedFrame.actOnVector, r, hπ]
  let σ : PeriodicLattice.FourTorus L n ≃ PeriodicLattice.FourTorus L n :=
    (PeriodicLattice.SignedFrame.torusEquiv L n r).trans
      (Equiv.addRight (PeriodicLattice.toFourTorus L n v))
  have hσind : PeriodicLattice.IsInducedByAffine σ r v := by
    intro x
    funext μ
    rcases Int.units_eq_one_or (s μ) with h | h <;>
      simp [σ, r, PeriodicLattice.SignedFrame.torusEquiv, PeriodicLattice.signedCoordinatePerm,
        PeriodicLattice.toFourTorus, PeriodicLattice.SignedFrame.actOnVector, h]
  refine ⟨σ, fun x => ?_, ?_⟩
  · obtain ⟨y, rfl⟩ : ∃ y : Fin 4 → ℝ, PeriodicLattice.toFourTorus L n y = x := by
      refine ⟨fun μ => Function.surjInv (QuotientAddGroup.mk_surjective) (x μ), ?_⟩
      funext μ
      exact Function.surjInv_eq QuotientAddGroup.mk_surjective (x μ)
    rw [hσind y, hr y]
    exact (hwv y).symm
  · obtain ⟨N, hN⟩ := hv
    refine ⟨r, v, ⟨N, fun μ => ?_⟩, hσind⟩
    rw [meshSize_levelDepth]
    exact hN μ
theorem vertexImage_eq_sitePreimage
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    {σ : PeriodicLattice.FourTorus L n ≃ PeriodicLattice.FourTorus L n} (hσf : ∀ x, σ x = f x)
    (x : Vertex L n k i) : vertexImage f x = PeriodicLattice.sitePreimage σ.symm x := by
  unfold vertexImage PeriodicLattice.sitePreimage
  rw [Equiv.symm_symm, hσf]
theorem vertexPreimage_eq {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hf : Function.Injective f) {x x' : Vertex L n k i} (h : f x' = x) :
    vertexPreimage f x = x' := by
  have hs : f (vertexPreimage f x) = x :=
    Classical.epsilon_spec (p := fun y : Vertex L n k i => f y = x) ⟨x', h⟩
  exact Subtype.ext (hf (hs.trans h.symm))
theorem pushField_eq_transportGaugeField
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    {σ : PeriodicLattice.FourTorus L n ≃ PeriodicLattice.FourTorus L n} (hσf : ∀ x, σ x = f x)
    (hedges : MapsEdgesOnto k i f) (U : Edge L n k i → Matrices.ComplexMatrix2) :
    pushField f U = PeriodicLattice.transportGaugeField σ U := by
  have hinj : Function.Injective f := by
    have : f = σ := funext fun x => (hσf x).symm
    rw [this]
    exact σ.injective
  funext e
  obtain ⟨e₀, hs, ht⟩ := hedges.2 e
  have hex : ∃ e' : Edge L n k i,
      (e'.source : PeriodicLattice.FourTorus L n) = σ.symm e.source ∧
      (e'.target : PeriodicLattice.FourTorus L n) = σ.symm e.target :=
    ⟨e₀, by rw [hs, ← hσf, Equiv.symm_apply_apply], by rw [ht, ← hσf, Equiv.symm_apply_apply]⟩
  have h1 : PeriodicLattice.bondPreimage σ e = e₀ := by
    simp only [PeriodicLattice.bondPreimage, dif_pos hex]
    have hc := hex.choose_spec
    refine PeriodicLattice.Bond.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [hc.1, hs, ← hσf, Equiv.symm_apply_apply]
    · rw [hc.2, ht, ← hσf, Equiv.symm_apply_apply]
  have h2 : edgePreimage f e = e₀ := by
    have hp : (edgePreimage f e).source = vertexPreimage f e.source ∧
        (edgePreimage f e).target = vertexPreimage f e.target :=
      Classical.epsilon_spec (p := fun e' : Edge L n k i =>
        e'.source = vertexPreimage f e.source ∧ e'.target = vertexPreimage f e.target)
        ⟨e₀, (vertexPreimage_eq hinj hs.symm).symm, (vertexPreimage_eq hinj ht.symm).symm⟩
    refine PeriodicLattice.Bond.ext ?_ ?_
    · rw [hp.1, vertexPreimage_eq hinj hs.symm]
    · rw [hp.2, vertexPreimage_eq hinj ht.symm]
  simp only [pushField, PeriodicLattice.transportGaugeField, h1, h2]
theorem meanContourHolonomy_transport
    (hC : PeriodicLattice.IsometryCovariance.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {a a' : ℤ} (ha : -(n : ℤ) ≤ a)
    (haa : a' = a + 1) {σ : PeriodicLattice.FourTorus L n ≃ PeriodicLattice.FourTorus L n}
    (hσ : σ ∈ PeriodicLattice.latticeIsometries L n a)
    {U : PeriodicLattice.Bond L n a' → Matrices.ComplexMatrix2}
    (hU : U ∈ PeriodicLattice.compactGaugeFields L n a') (y : PeriodicLattice.Site L n a)
    (x : PeriodicLattice.Site L n a') (hx : x ∈ PeriodicLattice.sitesInBlock a' y)
    (hh : PeriodicLattice.HasContourMean U y x) :
    PeriodicLattice.meanContourHolonomy (PeriodicLattice.transportGaugeField σ U)
        (PeriodicLattice.sitePreimage σ.symm y) (PeriodicLattice.sitePreimage σ.symm x) =
      PeriodicLattice.meanContourHolonomy U y x := by
  subst haa
  obtain ⟨ε, hε⟩ := hC
  exact (((hε L n hL hn a ha σ hσ).1 a le_rfl).2.2.2 y x univ U hx (fun _ _ => mem_univ _) hU
    fun _ _ _ _ => mem_univ _).2.2 hh
theorem smoothingEquivariantOnSides
    (hT : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hC : PeriodicLattice.IsometryCovariance.Statement)
    (hM : PeriodicLattice.AveragingMapsEquivariant)
    (hS : SmoothingAnalyticCovariantOnSides)
    (hX : PeriodicLattice.LevelBondOrientationDichotomy) : SmoothingEquivariantOnSides := by
  intro L hL n k j hn hj f hf hm
  have hL0 : 0 < L := by have := hL.2; omega
  have hk : 0 < k := by omega
  obtain ⟨⟨w, hw, v, hv, hwv⟩, hrest⟩ :=
    (hT L hL0 hL k).2.2.2.1 n hn (j + 1) hj f hf hm
  obtain ⟨σ, hσf, hσ⟩ := exists_mem_latticeIsometries hw hv hwv
  obtain ⟨-, hej₁, -⟩ := hrest (j + 1) le_rfl
  obtain ⟨-, hej, -⟩ := hrest j (Nat.le_succ j)
  have hi : -(n : ℤ) ≤ PeriodicLattice.levelDepth k (j + 1) := by
    simp only [PeriodicLattice.levelDepth]
    omega
  have hdepth : PeriodicLattice.levelDepth k j = PeriodicLattice.levelDepth k (j + 1) + 1 := by
    simp only [PeriodicLattice.levelDepth]
    omega
  obtain ⟨W, hW, -, hcontour⟩ := (hS L hL n k j hn hj).analytic
  have hstep := (hM L n hL hn _ hi σ hσ k).1 j hj le_rfl
  unfold EventuallyNearIdentity
  filter_upwards [eventually_mem_of_isOpenNhdOfOne hX hL hn hk (Nat.le_of_lt hj) hW,
    self_mem_nhdsWithin] with U hUW hU
  refine ⟨fun y x hx => ?_, ?_⟩
  · rw [pushField_eq_transportGaugeField hσf hej, vertexImage_eq_sitePreimage hσf,
      vertexImage_eq_sitePreimage hσf]
    exact meanContourHolonomy_transport hC hL hn hi hdepth hσ hU y x hx
      ((hcontour y x hx).1 U hUW)
  · rw [pushField_eq_transportGaugeField hσf hej, pushField_eq_transportGaugeField hσf hej₁]
    exact (hstep.2 U hU).2
end YangMills.Construction.Tower.EquivariantOnSides
end
