import YangMills.Construction.ChessboardTori.PeriodicGibbsStateAgainstOneTorusFromTheDefinition
import YangMills.Construction.ChessboardTori.TwoFormationsOfTheChessboardValue
import YangMills.Construction.SourcesAndGluing.ConfigurationsUnderLatticeSimilaritiesOfFourSpace
import YangMills.Construction.SourcesAndGluing.DominationByTheChessboard
import YangMills.Construction.SourcesAndGluing.GridsAndTheirGroups
import YangMills.Construction.SourcesAndGluing.WhatSimilaritiesCarry
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.ChessboardDominationProof
theorem le_liminf_of_eventually_mul_le {u : ℕ+ → ℝ} (hu : IsBoundedUnder (· ≤ ·) atTop u)
    {X N T : ℝ} (hT : 0 < T)
    (h : ∀ t, 0 < t → t < T → ∃ e : ℕ+ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ k in atTop, t * X ≤ t * u k + e k + t ^ 2 * N ^ 2) :
    X ≤ liminf u atTop := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hN : 0 < N ^ 2 + 1 := by positivity
  obtain ⟨t, ht0, htT, htN⟩ : ∃ t : ℝ, 0 < t ∧ t < T ∧ t * N ^ 2 ≤ ε / 2 := by
    refine ⟨min (T / 2) (ε / (2 * (N ^ 2 + 1))), lt_min (by linarith) (by positivity),
      (min_le_left _ _).trans_lt (by linarith), ?_⟩
    have h1 : min (T / 2) (ε / (2 * (N ^ 2 + 1))) ≤ ε / (2 * (N ^ 2 + 1)) := min_le_right _ _
    have h2 : ε / (2 * (N ^ 2 + 1)) * (N ^ 2 + 1) = ε / 2 := by
      field_simp
    have h3 := mul_le_mul_of_nonneg_right h1 hN.le
    have h4 : 0 ≤ min (T / 2) (ε / (2 * (N ^ 2 + 1))) :=
      le_min (by linarith) (by positivity)
    nlinarith
  obtain ⟨e, he, hk⟩ := h t ht0 htT
  have hsmall : ∀ᶠ k in atTop, e k < t * (ε / 2) := he.eventually_lt_const (by positivity)
  have hlow : ∀ᶠ k in atTop, X - ε ≤ u k := by
    filter_upwards [hk, hsmall] with k h1 h2
    have h4 : t ^ 2 * N ^ 2 ≤ t * (ε / 2) := by
      have := mul_le_mul_of_nonneg_left htN ht0.le
      nlinarith
    have h3 : t * (X - ε) ≤ t * u k := by nlinarith
    exact le_of_mul_le_mul_left h3 ht0
  have := le_liminf_of_le hu.isCoboundedUnder_ge hlow
  linarith
theorem liminf_finsetProd_le_prod_limsup {ι : Type*} (I : Finset ι) {x : ι → ℕ+ → ℝ}
    (h0 : ∀ i k, 0 ≤ x i k) (hb : ∀ i, IsBoundedUnder (· ≤ ·) atTop (x i)) :
    liminf (fun k => ∏ i ∈ I, x i k) atTop ≤ ∏ i ∈ I, limsup (x i) atTop := by
  have hcont : Continuous fun ε : ℝ => ∏ i ∈ I, (limsup (x i) atTop + ε) :=
    continuous_finsetProd _ fun i _ => continuous_const.add continuous_id
  have hlim : Tendsto (fun ε : ℝ => ∏ i ∈ I, (limsup (x i) atTop + ε)) (𝓝[>] 0)
      (𝓝 (∏ i ∈ I, limsup (x i) atTop)) := by
    have h := hcont.tendsto 0
    simp only [add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hev : ∀ᶠ k in atTop, ∀ i ∈ I, x i k ≤ limsup (x i) atTop + ε := by
    rw [Filter.eventually_all_finset]
    intro i _
    have hε' : (0 : ℝ) < ε := hε
    exact (eventually_lt_of_limsup_lt (by linarith) (hb i)).mono fun _ h => h.le
  have hprod : ∀ᶠ k in atTop, ∏ i ∈ I, x i k ≤ ∏ i ∈ I, (limsup (x i) atTop + ε) :=
    hev.mono fun k hk => Finset.prod_le_prod (fun i _ => h0 i k) hk
  exact liminf_le_of_frequently_le hprod.frequently
    (isBoundedUnder_of ⟨0, fun k => Finset.prod_nonneg fun i _ => h0 i k⟩)
theorem cubicGrid_eq_of_edge_origin {E : GluingSetup} {g₁ g₂ : CubicGrid E} (h₁ : g₁.edge = g₂.edge)
    (h₂ : g₁.origin = g₂.origin) : g₁ = g₂ := by
  cases g₁
  cases g₂
  simp only at h₁ h₂
  subst h₁ h₂
  rfl
theorem chessboardNorm_toMirror {E : GluingSetup} (G : CubicGrid E) (F : E.GridField → ℂ) :
    G.toMirror.chessboardNorm F = G.chessboardNorm F := by
  have hoff : G.toMirror.mirrorOrigin = G.mirrorOrigin :=
    G.toMirror.mirrorOrigin_of_isMirrorGrid G.toMirror_isMirrorGrid
  have hrefl : ∀ μ n, G.toMirror.wallReflection μ n = G.wallReflection μ n := fun μ n => by
    funext x
    simp only [CubicGrid.wallReflection, hoff]
    rfl
  have htor : ∀ μ n, G.toMirror.torusWallReflection μ n = G.torusWallReflection μ n :=
    fun μ n => by
      refine Equiv.ext fun x => ?_
      change TorusLifts.descendedMap _ _ (G.toMirror.wallReflection μ n) x =
        TorusLifts.descendedMap _ _ (G.wallReflection μ n) x
      rw [hrefl]
  have hgrp : G.toMirror.reflectionGroup = G.reflectionGroup := by
    simp only [CubicGrid.reflectionGroup, htor]
  have harr : G.toMirror.reflectionProduct F = G.reflectionProduct F := by
    funext U
    simp only [CubicGrid.reflectionProduct]
    rw [hgrp]
  simp only [CubicGrid.chessboardNorm, harr]
  rfl
def powerDilation (E : GluingSetup) (b : ℤ) (h0 : 0 ≤ b) (hK : b < ((E.K : ℕ) : ℤ)) :
    LatticeRescaling E :=
  ⟨b, h0, hK, 0, zero_mem _⟩
def dilatedSetup {E : GluingSetup} (Ψ : LatticeRescaling E) : ChessboardTori.ChessboardSetup :=
  ⟨⟨E.L, E.isAdmissible, Ψ.scaleExponent.targetCutoff, 1⟩, E.β, E.beta_pos⟩
def dilatedGrid {E : GluingSetup} (Ψ : LatticeRescaling E) (q : ℤ) (hq : 0 ≤ q)
    (c : InfiniteLattice.AmbientSpace)
    (hc : ∀ μ, ∃ i : ℤ, c μ = E.mesh * ((i : ℝ) + 1 / 2)) :
    ChessboardTori.ReflectionGrid (dilatedSetup Ψ) where
  q := q
  one_sub_K_le_q := by
    have : 0 < (((dilatedSetup Ψ).K : ℕ) : ℤ) := by exact_mod_cast (dilatedSetup Ψ).K.pos
    omega
  origin := Ψ.toSpace c
  origin_mem μ := by
    obtain ⟨i, hi⟩ := hc μ
    obtain ⟨n, hn⟩ := Ψ.base_mem
    refine ⟨i + n μ, ?_⟩
    have ha : (dilatedSetup Ψ).mesh = (E.L : ℝ) ^ Ψ.exp * E.mesh := Ψ.target_mesh_eq
    rw [ha]
    simp only [LatticeRescaling.toSpace, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hi, hn μ]
    push_cast
    ring
theorem precompose_mem_and_norm_eq (hW : RescalingTransportClaim)
    (hB : ChessboardTori.ChessboardNormComparison.Statement)
    {E : GluingSetup} (Ψ : LatticeRescaling E) (A : CubicGrid E) (hA : A.IsMirrorGrid)
    (g : ChessboardTori.ReflectionGrid (dilatedSetup Ψ)) (hg : g.IsCoarse)
    (hside : g.cellSide = (E.L : ℝ) ^ Ψ.exp * A.edge) (hoff : g.origin = Ψ.toSpace A.origin)
    (k : Fin 4 → ℤ) (F : E.GridField → ℂ) (hF : F ∈ A.cubeAlgebra k) :
    Ψ.precompose F ∈ ChessboardTori.ReflectionGrid.cellObservables (D := dilatedSetup Ψ) (g.cell k) ∧
      g.normAtExponent Ψ.scaleExponent.targetSideExponent (g.cell k) (Ψ.precompose F) =
        A.chessboardNorm F := by
  have h2 : 2 * g.cellSide ≤
      PeriodicLattice.torusSide (dilatedSetup Ψ).L Ψ.scaleExponent.targetSideExponent := by
    have h := A.isGridScale.2.2
    have hs : PeriodicLattice.torusSide E.L (Ψ.scaleExponent.targetSideExponent : ℕ) =
        (E.L : ℝ) ^ Ψ.exp * PeriodicLattice.torusSide E.L (E.m : ℕ) :=
      Ψ.scaleExponent.torusSide_target
    have hp := Ψ.zpow_L_pos
    change 2 * g.cellSide ≤ PeriodicLattice.torusSide E.L (Ψ.scaleExponent.targetSideExponent : ℕ)
    rw [hs, hside]
    have h' : 2 * A.edge ≤ PeriodicLattice.torusSide E.L (E.m : ℕ) := by
      have : A.edge ≤ PeriodicLattice.torusSide E.L (E.m : ℕ) / 2 := h
      linarith
    nlinarith
  obtain ⟨-, -, h, hobj, -, harr⟩ :=
    hB (dilatedSetup Ψ) g Ψ.scaleExponent.targetSideExponent E.cubeExp hg h2
  have hI : (g.toCubicGrid Ψ.scaleExponent.targetSideExponent E.cubeExp h :
      CubicGrid Ψ.scaleExponent.target) = Ψ.mappedGrid A hA :=
    cubicGrid_eq_of_edge_origin hside hoff
  have hc := (hW.1 E Ψ).2.2.2.2.2.2.2.2.2 A hA
  have hmem : Ψ.precompose F ∈ (Ψ.mappedGrid A hA).cubeAlgebra k := by
    rw [← (hc.2.1 k).1]
    exact ⟨F, hF, rfl⟩
  have hcell : (Ψ.mappedGrid A hA).cubeAlgebra k =
      ChessboardTori.ReflectionGrid.cellObservables (D := dilatedSetup Ψ) (g.cell k) := by
    rw [← hI]
    exact hobj.2.2.1 k
  have hmem' : Ψ.precompose F ∈
      ChessboardTori.ReflectionGrid.cellObservables (D := dilatedSetup Ψ) (g.cell k) :=
    hcell ▸ hmem
  refine ⟨hmem', ?_⟩
  have h3 := (harr (g.cell k) ⟨k, rfl⟩ (Ψ.precompose F) hmem').2
  have h4 := (hc.2.2.2 k F hF).2
  rw [h4, ← hI]
  exact h3.symm
theorem pull_pullInv {E : GluingSetup} (Ψ : LatticeRescaling E)
    (hsurj : Function.Surjective Ψ.pull) (U : E.GridField) :
    Ψ.pull (Ψ.pullInv U) = U :=
  haveI : Nonempty Ψ.scaleExponent.target.GridField := ⟨⟨fun _ => 1, fun _ => by simp⟩⟩
  Function.rightInverse_invFun hsurj U
theorem continuous_pullInv {E : GluingSetup} (Ψ : LatticeRescaling E)
    (hsurj : Function.Surjective Ψ.pull)
    (hlink : Function.Surjective Ψ.toMotion.onLink) :
    Continuous Ψ.pullInv := by
  have hr := pull_pullInv Ψ hsurj
  have hval : Continuous fun U => (Ψ.pullInv U).1 := continuous_pi fun c' => by
    obtain ⟨c, rfl⟩ := hlink c'
    have h : (fun U => (Ψ.pullInv U).1 (Ψ.toMotion.onLink c)) =
        fun U : E.GridField => U.1 c :=
      funext fun U => congrArg (fun W : E.GridField => W.1 c) (hr U)
    rw [h]
    exact (continuous_apply c).comp continuous_subtype_val
  exact continuous_induced_rng.2 hval
theorem integral_pushMeasure_comp_pull (hW : RescalingTransportClaim)
    (hC : FieldsUnderScaledMotionsOfSpace.Statement)
    {E : GluingSetup} (Ψ : LatticeRescaling E) (ν : Measure E.GridField)
    {A : E.GridField → ℂ} (hA : Measurable A) :
    ∫ U', A (Ψ.pull U') ∂Ψ.pushMeasure ν = ∫ U, A U ∂ν := by
  obtain ⟨hbij, hcont, -⟩ := hC E Ψ.scaleExponent Ψ.toMotion
  have hinv : Continuous Ψ.pullInv :=
    continuous_pullInv Ψ hbij.2 (hW.1 E Ψ).1.2.1
  have hcont' : Continuous Ψ.pull := hcont
  have hr := pull_pullInv Ψ hbij.2
  have hm : Measurable fun U' => A (Ψ.pull U') := hA.comp hcont'.measurable
  rw [LatticeRescaling.pushMeasure,
    integral_map hinv.measurable.aemeasurable hm.aestronglyMeasurable]
  simp only [hr]
theorem max_zero_neg_lt_K {D : GluingSetup} (s : D.ScaleAndOrigin) {j : ℤ}
    (hj : s.scale = (D.L : ℝ) ^ j) : max 0 (-j) < ((D.K : ℕ) : ℤ) := by
  have hL := D.one_lt_L
  have hL0 : (D.L : ℝ) ≠ 0 := by linarith
  have ha : D.mesh = (D.L : ℝ) ^ (-((D.K : ℕ) : ℤ)) := rfl
  have h2 : (D.L : ℝ) ^ 2 = (D.L : ℝ) ^ (2 : ℤ) := (zpow_ofNat _ 2).symm
  have h := s.le_scale
  rw [hj, ha, h2, ← zpow_add₀ hL0, zpow_le_zpow_iff_right₀ hL] at h
  have hK : 0 < ((D.K : ℕ) : ℤ) := by exact_mod_cast D.K.pos
  omega
theorem finprod_mem_image_cell {M : Type*} [CommMonoid M] {Dt : ChessboardTori.ChessboardSetup}
    (g : ChessboardTori.ReflectionGrid Dt) (I : Finset (Fin 4 → ℤ))
    (f : Set InfiniteLattice.AmbientSpace → M) :
    ∏ᶠ S ∈ g.cell '' (I : Set (Fin 4 → ℤ)), f S = ∏ i ∈ I, f (g.cell i) := by
  rw [finprod_mem_image g.cell_injective.injOn, finprod_mem_coe_finset]
theorem chessboardDomination_holds (hG : CubicGridsAndReflectionGroups.Statement)
    (hW : RescalingTransportClaim)
    (hC : FieldsUnderScaledMotionsOfSpace.Statement)
    (hB : ChessboardTori.ChessboardNormComparison.Statement)
    (hS : ChessboardTori.PeriodicGibbsBoundOfFiniteIndex.Statement) :
    ChessboardDomination := by
  intro D s ν hν n hmono htend F hF hfin
  obtain ⟨j, hj⟩ := s.scale_eq_zpow
  have hbK := max_zero_neg_lt_K s hj
  obtain ⟨b, hbdef⟩ : ∃ b : ℤ, b = max 0 (-j) := ⟨_, rfl⟩
  rw [← hbdef] at hbK
  have hb0 : 0 ≤ b := hbdef ▸ le_max_left _ _
  have hq : 0 ≤ j + b := by
    have : -j ≤ b := hbdef ▸ le_max_right _ _
    omega
  let Ψ : LatticeRescaling D := powerDilation D b hb0 hbK
  let Ψk : (m : ℕ+) → LatticeRescaling (D.withCutoffAndSide D.K m) :=
    fun m => powerDilation _ b hb0 hbK
  let mm : ℕ+ → ℕ+ := fun k => (Ψk (n k)).scaleExponent.targetSideExponent
  let cd : InfiniteLattice.AmbientSpace :=
    fun μ => D.mesh * ((⌊s.origin μ / D.mesh⌋ : ℝ) + 1 / 2)
  let g : ChessboardTori.ReflectionGrid (dilatedSetup Ψ) :=
    dilatedGrid Ψ (j + b) hq cd fun μ => ⟨_, rfl⟩
  have hgrid : g.IsCoarse := hq
  have hL0 : (D.L : ℝ) ≠ 0 := by linarith [D.one_lt_L]
  have hside : g.cellSide = (D.L : ℝ) ^ b * s.scale := by
    change (D.L : ℝ) ^ (j + b) = _
    rw [hj, zpow_add₀ hL0, mul_comm]
  have key : ∀ (k : ℕ+) (_ : 2 * s.scale ≤ (D.withCutoffAndSide D.K (n k)).side)
      (i : Fin 4 → ℤ),
      Ψ.precompose (F i) ∈
          ChessboardTori.ReflectionGrid.cellObservables (D := dilatedSetup Ψ) (g.cell i) ∧
        g.normAtExponent (mm k) (g.cell i) (Ψ.precompose (F i)) =
          s.normAt (n k) (F i) := by
    intro k h i
    have hfacts := hG _ (s.gridAt (n k) h) j hj
    have hFa : F i ∈ (s.gridAt (n k) h).toMirror.cubeAlgebra i := by
      rw [← hfacts.2.2.1.2.2.2 i]
      exact hF k h i
    have ht := precompose_mem_and_norm_eq hW hB (Ψk (n k)) (s.gridAt (n k) h).toMirror
      (s.gridAt (n k) h).toMirror_isMirrorGrid g hgrid hside rfl i (F i) hFa
    refine ⟨ht.1, ?_⟩
    simp only [GluingSetup.ScaleAndOrigin.normAt, dif_pos h]
    exact ht.2.trans (chessboardNorm_toMirror (s.gridAt (n k) h) (F i))
  let I : Finset (Fin 4 → ℤ) := hfin.toFinset
  let v : (Fin 4 → ℤ) → ℕ+ → ℝ := fun i k => s.normAt (n k) (F i)
  have hFone : ∀ i, i ∉ I → F i = 1 := fun i hi => by
    by_contra hne
    exact hi (hfin.mem_toFinset.2 hne)
  have hev : ∀ᶠ k in atTop, 2 * s.scale ≤ (D.withCutoffAndSide D.K (n k)).side :=
    htend.eventually_ge_atTop _
  have hone : ∀ (k : ℕ+) (_ : 2 * s.scale ≤ (D.withCutoffAndSide D.K (n k)).side)
      (i : Fin 4 → ℤ), i ∉ I → v i k = 1 := by
    intro k h i hi
    have hfacts := hG _ (s.gridAt (n k) h) j hj
    simp only [v, GluingSetup.ScaleAndOrigin.normAt, dif_pos h, hFone i hi]
    exact hfacts.2.2.2.2.2.2
  have hv0 : ∀ i k, 0 ≤ v i k := by
    intro i k
    simp only [v, GluingSetup.ScaleAndOrigin.normAt]
    split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_rfl
  have hnorm0 : ∀ {a : ℝ} (A : InfiniteLattice.GaugeField a → ℂ),
      0 ≤ InfiniteLattice.observableSupNorm A :=
    fun A => Real.iSup_nonneg fun _ => norm_nonneg _
  have hvB : ∀ i k, v i k ≤ InfiniteLattice.observableSupNorm (F i) := by
    intro i k
    by_cases h : 2 * s.scale ≤ (D.withCutoffAndSide D.K (n k)).side
    · have hfacts := hG _ (s.gridAt (n k) h) j hj
      simp only [v, GluingSetup.ScaleAndOrigin.normAt, dif_pos h]
      exact (hfacts.2.2.2.2.2.1 i (F i) (hF k h i)).2.2.2
    · simp only [v, GluingSetup.ScaleAndOrigin.normAt, dif_neg h]
      exact hnorm0 _
  have hbd : ∀ i, IsBoundedUnder (· ≤ ·) atTop (v i) := fun i =>
    isBoundedUnder_of ⟨_, hvB i⟩
  let w : ℕ+ → ℝ := fun k => ∏ i ∈ I, v i k
  have hwb : IsBoundedUnder (· ≤ ·) atTop w := isBoundedUnder_of
    ⟨∏ i ∈ I, InfiniteLattice.observableSupNorm (F i), fun k =>
      Finset.prod_le_prod (fun i _ => hv0 i k) fun i _ => hvB i k⟩
  have hueq : ∀ᶠ k in atTop, ∏ᶠ i, s.normAt (n k) (F i) = w k := by
    filter_upwards [hev] with k h
    refine finprod_eq_prod_of_mulSupport_subset _ fun i hi => ?_
    by_contra hni
    exact hi (hone k h i hni)
  have hFprod : ∀ U, ∏ᶠ i, F i U = ∏ i ∈ I, F i U := fun U => by
    refine finprod_eq_prod_of_mulSupport_subset _ fun i hi => ?_
    by_contra hni
    exact hi (by
      change F i U = 1
      rw [hFone i hni]
      rfl)
  have hlimsup : ∏ᶠ i, limsup (fun k => s.normAt (n k) (F i)) atTop =
      ∏ i ∈ I, limsup (v i) atTop := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun i hi => ?_
    by_contra hni
    exact hi ((limsup_congr (hev.mono fun k h => hone k h i hni)).trans (limsup_const 1))
  rw [liminf_congr hueq, hlimsup]
  refine ⟨?_, liminf_finsetProd_le_prod_limsup I hv0 hbd⟩
  obtain ⟨k₀, h₀⟩ := hev.exists
  have hν₀ : InfiniteLattice.IsPeriodicGibbs D.β ν := hν
  have hprob : IsProbabilityMeasure ν := hν₀.1.1
  let ν' := Ψ.pushMeasure ν
  have hν' : ν' ∈ (dilatedSetup Ψ).periodicStates :=
    ((hW.1 D Ψ).2.2.2.2.2.2.2.1 ν hprob).1 hν
  obtain ⟨Γ, hfi, hinv⟩ :=
    (show InfiniteLattice.IsPeriodicGibbs (dilatedSetup Ψ).β ν' from hν').2
  let O : Set (Set InfiniteLattice.AmbientSpace) := g.cell '' (I : Set (Fin 4 → ℤ))
  let F' : Set InfiniteLattice.AmbientSpace → (dilatedSetup Ψ).GaugeField → ℂ :=
    fun S => Ψ.precompose (F (Function.invFun g.cell S))
  have hF'c : ∀ i, F' (g.cell i) = Ψ.precompose (F i) := fun i =>
    congrArg (fun x => Ψ.precompose (F x)) (Function.leftInverse_invFun g.cell_injective i)
  have hO : g.IsFiniteCellFamily O :=
    ⟨I.finite_toSet.image _, by
      rintro S ⟨i, -, rfl⟩
      exact ⟨i, rfl⟩⟩
  have hF'mem : ∀ S ∈ O,
      F' S ∈ ChessboardTori.ReflectionGrid.cellObservables (D := dilatedSetup Ψ) S := by
    rintro S ⟨i, -, rfl⟩
    rw [hF'c]
    exact (key k₀ h₀ i).1
  have hmeas : Measurable fun U => ∏ i ∈ I, F i U :=
    Finset.measurable_prod I fun i _ => (hF k₀ h₀ i).1.1
  have hX : ∫ U, ∏ᶠ i, F i U ∂ν = ∫ U', ∏ᶠ S ∈ O, F' S U' ∂ν' := by
    have h1 : ∀ U', ∏ᶠ S ∈ O, F' S U' = ∏ i ∈ I, F i (Ψ.pull U') := fun U' => by
      rw [finprod_mem_image_cell g I fun S => F' S U']
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hF'c]
      rfl
    have h2 : ∫ U', ∏ᶠ S ∈ O, F' S U' ∂ν' = ∫ U', ∏ i ∈ I, F i (Ψ.pull U') ∂ν' :=
      integral_congr_ae (Eventually.of_forall h1)
    rw [h2]
    simp only [hFprod]
    exact (integral_pushMeasure_comp_pull hW hC Ψ ν hmeas).symm
  let N : ℝ := InfiniteLattice.observableSupNorm
    fun U : (dilatedSetup Ψ).GaugeField => ∏ᶠ S ∈ O, F' S U
  have hN0 : 0 ≤ N := hnorm0 _
  have hpos : 0 < (D.L : ℝ) ^ b := zpow_pos (by linarith [D.one_lt_L]) _
  have htm : Tendsto (fun k => PeriodicLattice.torusSide (dilatedSetup Ψ).L (mm k))
      atTop atTop := by
    have hs : ∀ k, (D.L : ℝ) ^ b * (D.withCutoffAndSide D.K (n k)).side =
        PeriodicLattice.torusSide (dilatedSetup Ψ).L (mm k) := fun k =>
      ((Ψk (n k)).scaleExponent.torusSide_target).symm
    exact (Tendsto.const_mul_atTop hpos htend).congr hs
  have hev2 : ∀ᶠ k in atTop, 2 * (g.enclosingCoarsening O).cellSide ≤
      PeriodicLattice.torusSide (dilatedSetup Ψ).L (mm k) := htm.eventually_ge_atTop _
  have hsurf : Tendsto (fun k => (2 * (Γ.index : ℝ)) ^ 4 * g.coarseSurfaceTerm O (mm k))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => (g.enclosingCoarsening O).cellSide /
        PeriodicLattice.torusSide (dilatedSetup Ψ).L (mm k)) atTop (𝓝 0) :=
      htm.const_div_atTop _
    have h2 := (h1.const_mul ((Constants.SurfaceTerms.surfaceFactor : ℝ) * (dilatedSetup Ψ).β *
      ((g.enclosingCoarsening O).cellSide / (dilatedSetup Ψ).mesh) ^ 3)).const_mul
      ((2 * (Γ.index : ℝ)) ^ 4)
    simp only [mul_zero] at h2
    exact h2
  rw [hX]
  refine le_liminf_of_eventually_mul_le hwb (N := N) (T := (2 * N + 1)⁻¹) (by positivity)
    fun t ht0 ht1 => ⟨_, hsurf, ?_⟩
  filter_upwards [hev, hev2] with k h h2
  have hest := hS (dilatedSetup Ψ) g hgrid ν' hν' O hO F' hF'mem Γ Γ.index hfi rfl hinv (mm k)
    h2 t ht0 ht1
  have hprod : ∏ᶠ S ∈ O, g.normAtExponent (mm k) S (F' S) = w k := by
    rw [finprod_mem_image_cell g I fun S => g.normAtExponent (mm k) S (F' S)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hF'c]
    exact (key k h i).2
  rw [hprod] at hest
  exact hest
end YangMills.Construction.SourcesAndGluing.ChessboardDominationProof
end
