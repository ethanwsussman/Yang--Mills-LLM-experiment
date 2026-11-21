import YangMills.Construction.ChessboardTori.ElementaryPropertiesOfAGrid
import YangMills.Construction.ChessboardTori.FromTheInfiniteLatticeToTheTorus
import YangMills.Construction.ChessboardTori.GroupOfAGridAndCopies
import YangMills.Construction.ChessboardTori.ObservablesMeasurableInASetAndTheirRestrictionToATorusProof
import YangMills.Construction.ChessboardTori.TwoFormationsOfTheChessboardValue
import YangMills.Construction.InfiniteLattice.SpaceOfTheConfigurationsOnALatticeAndItsObservables
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusLifts
open scoped MeasureTheory
namespace ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace NormAgreement
section RotationPart
open SourcesAndGluing
def signedDiagonal (s : Fin 4 → ℤˣ) : Equiv.Perm AmbientSpace := signedCoordinateEquiv 1 s
theorem entry_eq_of_sub_mem_lattice {ℓ : ℝ} (hℓ : ℓ ≠ 0) {S S' : Equiv.Perm AmbientSpace}
    (hS : S ∈ hyperoctahedralGroupEuclidean) (hS' : S' ∈ hyperoctahedralGroupEuclidean)
    (h : ∀ x, ∃ k : Fin 4 → ℤ, S' x = S x + TestFunctions.latticeTranslate ℓ k) (μ ν : Fin 4) :
    S' (stdBasis μ) ν = S (stdBasis μ) ν := by
  obtain ⟨π, s, rfl⟩ := hS
  obtain ⟨π', s', rfl⟩ := hS'
  obtain ⟨k, hk⟩ := h ((ℓ / 3) • stdBasis μ)
  have hν := congrFun hk ν
  have hval : ∀ (ρ : Equiv.Perm (Fin 4)) (e : Fin 4 → ℤˣ) (t : ℝ),
      signedCoordinateEquiv ρ e (t • stdBasis μ) ν =
        t * (((e ν : ℤ) * (if ρ ν = μ then 1 else 0) : ℤ) : ℝ) := by
    intro ρ e t
    change ((e ν : ℤ) : ℝ) * (t • stdBasis μ) (ρ ν) = _
    by_cases hρ : ρ ν = μ
    · simp [hρ, stdBasis]
      ring
    · simp [hρ, stdBasis]
  have hone : ∀ (ρ : Equiv.Perm (Fin 4)) (e : Fin 4 → ℤˣ),
      signedCoordinateEquiv ρ e (stdBasis μ) ν =
        (((e ν : ℤ) * (if ρ ν = μ then 1 else 0) : ℤ) : ℝ) := by
    intro ρ e
    have := hval ρ e 1
    simpa using this
  have hb : ∀ (ρ : Equiv.Perm (Fin 4)) (e : Fin 4 → ℤˣ),
      (e ν : ℤ) * (if ρ ν = μ then 1 else 0) ∈ ({-1, 0, 1} : Set ℤ) := by
    intro ρ e
    rcases Int.units_eq_one_or (e ν) with h1 | h1 <;> by_cases hρ : ρ ν = μ <;> simp [h1, hρ]
  rw [hone, hone]
  rw [hval, Pi.add_apply, hval] at hν
  set A : ℤ := (s' ν : ℤ) * (if π' ν = μ then 1 else 0) with hA
  set B : ℤ := (s ν : ℤ) * (if π ν = μ then 1 else 0) with hB
  have hper : TestFunctions.latticeTranslate ℓ k ν = (k ν : ℝ) * ℓ := by
    simp [TestFunctions.latticeTranslate, mul_comm]
  rw [hper] at hν
  have h3 : (A : ℝ) = (B : ℝ) + 3 * (k ν : ℝ) := by
    have : ℓ * ((A : ℝ) - B - 3 * k ν) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hℓ
    · linarith
  have h4 : A = B + 3 * k ν := by exact_mod_cast h3
  have hA' := hb π' s'
  have hB' := hb π s
  simp only [mem_insert_iff, mem_singleton_iff, ← hA, ← hB] at hA' hB'
  have h5 : A = B := by omega
  rw [h5]
theorem rotationDet_signedDiagonal (s : Fin 4 → ℤˣ) :
    rotationDet (signedDiagonal s) = ∏ μ, ((s μ : ℤ) : ℝ) := by
  have hM : (Matrix.of fun ν μ => signedDiagonal s (stdBasis μ) ν : Matrix _ _ ℝ) =
      Matrix.diagonal fun ν => ((s ν : ℤ) : ℝ) := by
    ext ν μ
    by_cases h : ν = μ
    · subst h
      simp [signedDiagonal, signedCoordinateEquiv, PeriodicLattice.CutoffTorus.signedPermEuclidean,
        stdBasis]
    · simp [signedDiagonal, signedCoordinateEquiv, PeriodicLattice.CutoffTorus.signedPermEuclidean,
        stdBasis, Matrix.diagonal_apply_ne _ h, Pi.single_eq_of_ne h]
  rw [rotationDet, hM, Matrix.det_diagonal]
variable {E : SourcesAndGluing.GluingSetup}
theorem hasRotationPart_signedDiagonal (s : Fin 4 → ℤˣ) (w : AmbientSpace) (hw : w ∈ E.gridPoints)
    (r : AmbientSpace → AmbientSpace) (hr : ∀ x, r x = signedDiagonal s x + w)
    (r' : E.Torus → E.Torus) (hc : ∀ x, E.proj (r x) = r' (E.proj x)) :
    SourcesAndGluing.HasRotationPart r' (signedDiagonal s) := by
  have himage : E.trivialExponent.target.mesh = E.mesh :=
    (congrArg (PeriodicLattice.meshSize E.L) E.trivialExponent.target_K).trans
      (by simp [GluingSetup.trivialExponent]; rfl)
  refine ⟨⟨signedDiagonal s, ⟨1, s, rfl⟩, w, ?_⟩, rfl, ?_⟩
  · change w ∈ InfiniteLattice.latticeSubgroup E.trivialExponent.target.mesh
    rw [himage]
    exact hw
  · funext x
    have h1 := hc x
    rw [hr] at h1
    change r' (E.proj x) = E.proj _
    rw [← h1]
    simp [ScaledLatticeMotion.onSpace, scaledMotion, GluingSetup.trivialExponent]
theorem orientationSign_signedDiagonal (s : Fin 4 → ℤˣ) (r' : E.Torus → E.Torus)
    (h : SourcesAndGluing.HasRotationPart r' (signedDiagonal s)) :
    (((SourcesAndGluing.orientationSign r' : ℤˣ) : ℤ) : ℝ) = ∏ μ, ((s μ : ℤ) : ℝ) := by
  rw [orientationSign_eq_rotationDet h, ← rotationDet_signedDiagonal]
  have h' : SourcesAndGluing.HasRotationPart r' (rotationPart r') := Classical.epsilon_spec ⟨_, h⟩
  obtain ⟨Φ, hΦ, hI⟩ := h
  obtain ⟨Φ', hΦ', hI'⟩ := h'
  have hℓ : PeriodicLattice.torusSide E.L E.m ≠ 0 := by
    have := E.one_lt_L
    simp only [PeriodicLattice.torusSide]
    positivity
  have hS := Φ.rotation_mem
  have hS' := Φ'.rotation_mem
  have hadd : ∀ x, ∃ k : Fin 4 → ℤ, Φ'.rotation x = Φ.rotation x +
      TestFunctions.latticeTranslate (PeriodicLattice.torusSide E.L E.m) k := by
    have hsp : ∀ (Ψ : ScaledLatticeMotion E.trivialExponent) x,
        Ψ.onSpace x = Ψ.rotation x + Ψ.offset := by
      intro Ψ x
      simp [ScaledLatticeMotion.onSpace, scaledMotion, GluingSetup.trivialExponent]
    have hcov : ∀ x, TorusMetric.torusProj (PeriodicLattice.torusSide E.L E.m) (Φ'.onSpace x) =
        TorusMetric.torusProj (PeriodicLattice.torusSide E.L E.m) (Φ.onSpace x) := fun x =>
      (congrFun hI' x).symm.trans (congrFun hI x)
    have hzero : ∀ (Ψ : ScaledLatticeMotion E.trivialExponent), Ψ.rotation 0 = 0 := by
      intro Ψ
      have := map_add_of_mem_hyperoctahedral Ψ.rotation_mem 0 0
      simpa using this
    obtain ⟨k₀, hk₀⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq (hcov 0)
    intro x
    obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq (hcov x)
    refine ⟨k - k₀, ?_⟩
    rw [hsp, hsp, hzero, hzero] at hk₀
    rw [hsp, hsp] at hk
    funext ν
    have h1 := congrFun hk ν
    have h2 := congrFun hk₀ ν
    simp only [Pi.add_apply, TestFunctions.latticeTranslate, Pi.zero_apply, zero_add, Pi.sub_apply,
      Int.cast_sub] at h1 h2 ⊢
    linarith
  have hent := entry_eq_of_sub_mem_lattice hℓ hS hS' hadd
  rw [hΦ] at hent
  rw [hΦ'] at hent
  simp only [rotationDet]
  congr 1
  ext ν μ
  exact hent μ ν
end RotationPart
section Objects
variable {D : ChessboardSetup} (g : ReflectionGrid D) (m' : ℕ+) (i : ℕ)
theorem isGridScale_cellSide (hs : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L m') :
    (D.toGluingSetup m' i).IsGridScale g.cellSide := by
  refine ⟨⟨g.q, rfl⟩, ?_, ?_⟩
  · change (D.L : ℝ) ^ (-((D.K : ℕ) : ℤ)) ≤ (D.L : ℝ) ^ g.q
    refine zpow_le_zpow_right₀ D.one_lt_factor.le ?_
    have := g.one_sub_K_le_q
    omega
  · change g.cellSide ≤ PeriodicLattice.torusSide D.L m' / 2
    linarith
theorem K_eq_one_of_not_sq_mul_mesh_le (hg : g.IsCoarse)
    (h : ¬ (D.L : ℝ) ^ 2 * D.mesh ≤ g.cellSide) :
    (D.K : ℕ) = 1 ∧ g.cellSide = 1 := by
  have hL := D.one_lt_factor
  have hq : (0 : ℤ) ≤ g.q := hg
  have ha : (D.L : ℝ) ^ 2 * D.mesh = (D.L : ℝ) ^ (2 - ((D.K : ℕ) : ℤ)) := by
    have h1 : D.mesh = (D.L : ℝ) ^ (-((D.K : ℕ) : ℤ)) := rfl
    have h0 : (D.L : ℝ) ≠ 0 := by linarith
    rw [h1, sub_eq_add_neg, zpow_add₀ h0]
    norm_cast
  rw [ha, ReflectionGrid.cellSide, zpow_le_zpow_iff_right₀ hL, not_le] at h
  have hK := D.K.pos
  have hK1 : (D.K : ℕ) = 1 := by omega
  have hq0 : g.q = 0 := by omega
  exact ⟨hK1, by simp [ReflectionGrid.cellSide, hq0]⟩
theorem interior_cell (k : Fin 4 → ℤ) :
    interior (g.cell k) =
      {x | ∀ μ, x μ - (g.origin μ + g.cellSide * k μ) ∈ Ioo 0 g.cellSide} := by
  have h1 : g.cell k = Set.pi univ fun μ =>
      Icc (g.origin μ + g.cellSide * k μ) (g.origin μ + g.cellSide * k μ + g.cellSide) := by
    ext x
    simp only [ReflectionGrid.cell, mem_ofPred_eq, Set.mem_pi, mem_univ, true_imp_iff, mem_Icc]
    refine forall_congr' fun μ => ?_
    constructor <;> rintro ⟨h, h'⟩ <;> constructor <;> linarith
  rw [h1, interior_pi_set finite_univ]
  ext x
  simp only [Set.mem_pi, mem_univ, true_imp_iff, interior_Icc, mem_Ioo, mem_ofPred_eq]
  refine forall_congr' fun μ => ?_
  constructor <;> rintro ⟨h, h'⟩ <;> constructor <;> linarith
theorem eq_on_linksWithin_of_eq_on_positive {a : ℝ} {S : Set AmbientSpace}
    {U V : InfiniteLattice.GaugeField a}
    (h : ∀ b ∈ InfiniteLattice.positiveLinksWithin a S, U b = V b) :
    ∀ b ∈ InfiniteLattice.linksWithin (a := a) S, U b = V b := by apply _root_.YangMills.Construction.ChessboardTori.MeasurableObservables.eq_on_linksWithin <;> assumption
theorem cubeAlgebra_eq (hDep : MeasurableObservablesAndLifts.Statement)
    (hSp : InfiniteLattice.ConfigurationSpace.Main) (hg : g.IsCoarse)
    (h : (D.toGluingSetup m' i).IsGridScale g.cellSide) (k : Fin 4 → ℤ) :
    (g.toCubicGrid m' i h).cubeAlgebra k = ReflectionGrid.cellObservables (D := D) (g.cell k) := by
  have hOpen : (g.toCubicGrid m' i h).openCube k = interior (g.cell k) := by
    rw [interior_cell]
    rfl
  rw [(hDep D).2.2.1 g hg (g.cell k) ⟨k, rfl⟩]
  ext F
  simp only [SourcesAndGluing.CubicGrid.cubeAlgebra, mem_ofPred_eq, hOpen]
  refine and_congr_right fun hF => ?_
  constructor
  · intro hag
    obtain ⟨-, -, -, hd, -, hf, -⟩ := hSp D.mesh D.mesh_pos
    have hpos : InfiniteLattice.positiveLinksWithin D.mesh (interior (g.cell k)) ⊆
        InfiniteLattice.positiveLinkSet D.mesh := inter_subset_left
    have h2 : ∀ U V : InfiniteLattice.GaugeField D.mesh,
        InfiniteLattice.restrictField U
            (InfiniteLattice.positiveLinksWithin D.mesh (interior (g.cell k))) =
          InfiniteLattice.restrictField V
            (InfiniteLattice.positiveLinksWithin D.mesh (interior (g.cell k))) → F U = F V := by
      intro U V hUV
      exact hag U V (eq_on_linksWithin_of_eq_on_positive fun b hb => congrFun hUV ⟨b, hb⟩)
    have h12 := ((hd.1 _ hpos F hF).1.out 0 1).2 h2
    exact Eq.mpr (congrArg (fun m => @Measurable _ _ m _ F) (hf.1 (interior (g.cell k)))) h12
  · intro hm U V hUV
    exact (hDep D).1 _ F hF hm U V fun b hb => hUV b hb.2
theorem cubicGridObjectsAgree (hDep : MeasurableObservablesAndLifts.Statement)
    (hSp : InfiniteLattice.ConfigurationSpace.Main) (hg : g.IsCoarse)
    (h : (D.toGluingSetup m' i).IsGridScale g.cellSide) :
    g.CubicGridObjectsAgree m' i h := by
  have hM : (g.toCubicGrid m' i h).IsMirrorGrid := g.origin_mem
  exact ⟨fun _ => rfl, fun _ _ => rfl, cubeAlgebra_eq g m' i hDep hSp hg h, hM,
    SourcesAndGluing.CubicGrid.toMirror_of_isMirrorGrid _ hM⟩
end Objects
section Group
variable {D : ChessboardSetup} (g : ReflectionGrid D) (m' : ℕ+) (i : ℕ)
theorem wallReflection_eq (h : (D.toGluingSetup m' i).IsGridScale g.cellSide) (μ : Fin 4) (n : ℤ)
    (x : AmbientSpace) : (g.toCubicGrid m' i h).wallReflection μ n x = g.reflect μ n x := by
  have hM : (g.toCubicGrid m' i h).IsMirrorGrid := g.origin_mem
  have h1 := (g.toCubicGrid m' i h).mirrorOrigin_of_isMirrorGrid hM
  simp only [SourcesAndGluing.CubicGrid.wallReflection, h1]
  rfl
theorem exists_descent_hom (hGrid : ReflectionGroupAndTransport.Statement) (hg : g.IsCoarse)
    (hs : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L m')
    (h : (D.toGluingSetup m' i).IsGridScale g.cellSide) :
    ∃ φ : (g.withExponent m').reflectionGroup →* Equiv.Perm (D.withExponent m').Torus,
      (∀ r : (g.withExponent m').reflectionGroup,
        (D.withExponent m').proj ∘ r.1 = φ r ∘ (D.withExponent m').proj) ∧
      (fun e : Equiv.Perm (D.withExponent m').Torus =>
          (e : (D.withExponent m').Torus → (D.withExponent m').Torus)) ''
        (φ.range : Set _) = (g.withExponent m').inducedTorusMaps ∧
      (g.toCubicGrid m' i h).reflectionGroup = φ.range := by
  obtain ⟨-, ⟨φ, hφ, -, himg, hcl⟩, -⟩ :=
    (hGrid (D.withExponent m') (g.withExponent m') hg).2.2.2.2.1 hs
  refine ⟨φ, hφ, himg, ?_⟩
  have hθ : ∀ (μ : Fin 4) (n : ℤ), (g.toCubicGrid m' i h).torusWallReflection μ n =
      φ ((g.withExponent m').reflectElem μ n) := by
    intro μ n
    refine Equiv.ext fun u => ?_
    obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
    have h1 := congrFun ((g.toCubicGrid m' i h).descends_torusWallReflection μ n) x
    have h2 := congrFun (hφ ((g.withExponent m').reflectElem μ n)) x
    refine h1.trans (Eq.trans ?_ h2)
    change TorusMetric.torusProj _ ((g.toCubicGrid m' i h).wallReflection μ n x) =
      TorusMetric.torusProj _ (g.reflect μ n x)
    rw [wallReflection_eq]
  rw [hcl]
  change Subgroup.closure _ = _
  congr 2
  funext p
  exact hθ p.1 p.2
theorem cubicGridGroupAgrees (hElem : GridBasicProperties.Statement)
    (hGrid : ReflectionGroupAndTransport.Statement) (hg : g.IsCoarse)
    (hs : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L m')
    (h : (D.toGluingSetup m' i).IsGridScale g.cellSide) :
    g.CubicGridGroupAgrees m' i h := by
  classical
  obtain ⟨φ, hφ, himg, hrange⟩ := exists_descent_hom g m' i hGrid hg hs h
  refine ⟨?_, ?_⟩
  · rw [hrange]
    exact himg
  intro r hr
  rw [hrange] at hr
  obtain ⟨r₀, rfl⟩ := hr
  have hE := hElem (D.withExponent m') (g.withExponent m')
  have hCW := hE.2.2.2.1
  have hGT := (hE.2.2.2.2.2.2 hs).2.1
  have hind : (D.withExponent m').proj ∘ ((g.withExponent m').inducingElement (φ r₀)).1 =
      φ r₀ ∘ (D.withExponent m').proj :=
    Classical.epsilon_spec (p := fun r : (g.withExponent m').reflectionGroup =>
      (D.withExponent m').proj ∘ r.1 = φ r₀ ∘ (D.withExponent m').proj) ⟨r₀, hφ r₀⟩
  have hs1 : (g.withExponent m').torusSign (φ r₀) = orientationSign r₀.1 :=
    hGT.2.2.2.1 _ ((g.withExponent m').inducingElement (φ r₀)).2 _ r₀.2 _ hind (hφ r₀)
  refine Eq.trans ?_ (hs1.trans (hCW.2.2.1 r₀.1 r₀.2)).symm
  let s : Fin 4 → ℤˣ := fun μ => if (g.withExponent m').ReflectsCoord r₀.1 μ then -1 else 1
  have hcoord : ∀ μ, ∃ (w : ℝ) (n : ℤ), w = (n : ℝ) * D.mesh ∧
      ∀ x, r₀.1 x μ = ((s μ : ℤ) : ℝ) * x μ + w := by
    intro μ
    obtain ⟨e, he⟩ := g.origin_mem μ
    have hside := g.cellSide_eq
    by_cases hf : (g.withExponent m').ReflectsCoord r₀.1 μ
    · have hsμ : s μ = -1 := if_pos hf
      obtain ⟨k, hk⟩ := hf
      refine ⟨2 * g.origin μ + 2 * k * g.cellSide, 2 * e + 1 + 2 * k * g.cellRatio, ?_,
        fun x => ?_⟩
      · rw [he, hside]
        push_cast
        ring
      · have h1 := hk x
        simp only [ReflectionGrid.coordReflect] at h1
        have h2 : r₀.1 x μ - g.origin μ = 2 * k * g.cellSide - (x μ - g.origin μ) := h1
        rw [hsμ]
        push_cast
        linarith
    · have hsμ : s μ = 1 := if_neg hf
      obtain ⟨t, ht⟩ := (hCW.1 r₀.1 r₀.2 μ).resolve_right hf
      refine ⟨2 * t * g.cellSide, 2 * t * g.cellRatio, ?_, fun x => ?_⟩
      · rw [hside]
        push_cast
        ring
      · have h1 := ht x
        simp only [ReflectionGrid.coordShift] at h1
        have h2 : r₀.1 x μ - g.origin μ = x μ - g.origin μ + 2 * t * g.cellSide := h1
        rw [hsμ]
        push_cast
        linarith
  choose w n hwn hw using hcoord
  have hmem : w ∈ (D.toGluingSetup m' i).gridPoints := ⟨n, fun μ => hwn μ⟩
  have hlin := hasRotationPart_signedDiagonal (E := D.toGluingSetup m' i) s w hmem r₀.1
    (fun x => funext fun μ => hw μ x) (φ r₀) (fun x => congrFun (hφ r₀) x)
  have hpar := orientationSign_signedDiagonal s _ hlin
  refine Units.ext (Int.cast_injective (α := ℝ) ?_)
  refine hpar.trans ?_
  have hprod : ∏ μ, ((s μ : ℤ) : ℝ) =
      ∏ μ, (if (g.withExponent m').ReflectsCoord r₀.1 μ then (-1 : ℝ) else 1) := by
    refine Finset.prod_congr rfl fun μ _ => ?_
    by_cases hf : (g.withExponent m').ReflectsCoord r₀.1 μ
    · simp [s, hf]
    · simp [s, hf]
  rw [hprod, Finset.prod_ite]
  simp [ReflectionGrid.numReflectedCoords]
end Group
section Product
variable {D : ChessboardSetup} (g : ReflectionGrid D) (m' : ℕ+) (i : ℕ)
theorem imageLink_eq_linkMap (rL : (D.toGluingSetup m' i).TorusLatticeIsometry)
    (b : (D.toGluingSetup m' i).PeriodicLink) :
    (D.withExponent m').imageLink rL.toFun b = rL.linkMap b := by
  have hex : ∃ b' : (D.withExponent m').PeriodicLink,
      (b'.source : (D.withExponent m').Torus) = rL.toFun b.source ∧
        (b'.target : (D.withExponent m').Torus) = rL.toFun b.target := ⟨rL.linkMap b, rfl, rfl⟩
  have hsp := Classical.epsilon_spec hex
  exact PeriodicLattice.Bond.ext (Subtype.ext hsp.1) (Subtype.ext hsp.2)
theorem reflectionProduct_eq (hElem : GridBasicProperties.Statement)
    (hGrid : ReflectionGroupAndTransport.Statement) (hg : g.IsCoarse)
    (hs : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L m')
    (h : (D.toGluingSetup m' i).IsGridScale g.cellSide) (F : D.GaugeField → ℂ) :
    (g.toCubicGrid m' i h).reflectionProduct F =
      (g.withExponent m').torusProduct ((D.withExponent m').liftedObservable F) := by
  have hB := cubicGridGroupAgrees g m' i hElem hGrid hg hs h
  have hGT := ((hElem (D.withExponent m') (g.withExponent m')).2.2.2.2.2.2 hs).2.1
  funext U
  have hcopy : ∀ r ∈ ((g.toCubicGrid m' i h).reflectionGroup : Set _),
      SourcesAndGluing.signedCopy (D := D.toGluingSetup m' i) r F U =
        (g.withExponent m').torusTransport r ((D.withExponent m').liftedObservable F) U := by
    intro r hr
    have hsign := hB.2 r hr
    have hmem : (r : (D.withExponent m').Torus → (D.withExponent m').Torus) ∈
        (g.withExponent m').inducedTorusMaps := by
      rw [← hB.1]
      exact ⟨r, hr, rfl⟩
    let rL : (D.toGluingSetup m' i).TorusLatticeIsometry :=
      ⟨r, ⟨r.bijective, hGT.2.2.1 _ hmem⟩, (hGT.2.2.2.2.1 _ hmem).1⟩
    have e1 : rL.toEquiv = r := Equiv.ext fun _ => rfl
    have h1 := SourcesAndGluing.signedCopy_eq_actOn rL F
    rw [e1] at h1
    rw [h1]
    have h2 : rL.actOn ((D.toGluingSetup m' i).pullToTorus F) =
        (D.withExponent m').pullbackObservable r ((D.withExponent m').liftedObservable F) := by
      funext W
      change (D.toGluingSetup m' i).pullToTorus F (rL.pullbackField W) =
        (D.withExponent m').liftedObservable F ((D.withExponent m').pullbackField r W)
      have h3 : rL.pullbackField W = (D.withExponent m').pullbackField r W := by
        funext b
        change W (rL.linkMap b) = W ((D.withExponent m').imageLink rL.toFun b)
        rw [imageLink_eq_linkMap]
      rw [h3]
      rfl
    rw [h2, hsign]
    rfl
  have hinj : InjOn (fun r : Equiv.Perm (D.toGluingSetup m' i).Torus =>
      (r : (D.toGluingSetup m' i).Torus → (D.toGluingSetup m' i).Torus))
      ((g.toCubicGrid m' i h).reflectionGroup : Set _) :=
    fun _ _ _ _ hab => Equiv.coe_fn_injective hab
  calc (g.toCubicGrid m' i h).reflectionProduct F U
      = ∏ᶠ r : ((g.toCubicGrid m' i h).reflectionGroup :
            Set (Equiv.Perm (D.toGluingSetup m' i).Torus)),
          SourcesAndGluing.signedCopy (D := D.toGluingSetup m' i) r.1 F U := rfl
    _ = ∏ᶠ (r : Equiv.Perm (D.toGluingSetup m' i).Torus)
          (_ : r ∈ ((g.toCubicGrid m' i h).reflectionGroup : Set _)),
          SourcesAndGluing.signedCopy (D := D.toGluingSetup m' i) r F U :=
        finprod_set_coe_eq_finprod_mem (f := fun r : Equiv.Perm (D.toGluingSetup m' i).Torus =>
          SourcesAndGluing.signedCopy (D := D.toGluingSetup m' i) r F U)
          ((g.toCubicGrid m' i h).reflectionGroup : Set _)
    _ = ∏ᶠ (r : Equiv.Perm (D.toGluingSetup m' i).Torus)
          (_ : r ∈ ((g.toCubicGrid m' i h).reflectionGroup : Set _)),
          (g.withExponent m').torusTransport (r : (D.withExponent m').Torus → (D.withExponent m').Torus)
            ((D.withExponent m').liftedObservable F) U :=
        finprod_mem_congr rfl hcopy
    _ = ∏ᶠ (r' : (D.toGluingSetup m' i).Torus → (D.toGluingSetup m' i).Torus)
          (_ : r' ∈ (fun r : Equiv.Perm (D.toGluingSetup m' i).Torus =>
            (r : (D.toGluingSetup m' i).Torus → (D.toGluingSetup m' i).Torus)) ''
            ((g.toCubicGrid m' i h).reflectionGroup : Set _)),
          (g.withExponent m').torusTransport r' ((D.withExponent m').liftedObservable F) U :=
        (finprod_mem_image (f := fun r' : (D.toGluingSetup m' i).Torus →
          (D.toGluingSetup m' i).Torus =>
            (g.withExponent m').torusTransport r' ((D.withExponent m').liftedObservable F) U)
            hinj).symm
    _ = (g.withExponent m').torusProduct ((D.withExponent m').liftedObservable F) U := by
        have h1 := hB.1
        change _ = (g.withExponent m').inducedTorusMaps at h1
        rw [h1]
        rfl
end Product
theorem chessboardNormComparison (hDep : MeasurableObservablesAndLifts.Statement)
    (hSp : InfiniteLattice.ConfigurationSpace.Main)
    (hElem : GridBasicProperties.Statement) (hGrid : ReflectionGroupAndTransport.Statement)
    (hBr : TorusReduction.Statement) :
    ChessboardNormComparison.Statement := by
  intro D g m' i hg hs
  have hgs := isGridScale_cellSide g m' i hs
  refine ⟨fun h => ⟨hgs, h⟩, K_eq_one_of_not_sq_mul_mesh_le g hg, hgs,
    cubicGridObjectsAgree g m' i hDep hSp hg hgs,
    cubicGridGroupAgrees g m' i hElem hGrid hg hs hgs, ?_⟩
  intro S hS F hF
  have hb := hBr (D.withExponent m') (g.withExponent m') hs
  obtain ⟨-, -, -, hprod, hval, -⟩ := hb
  have harr := reflectionProduct_eq g m' i hElem hGrid hg hs hgs F
  refine ⟨fun U hU => ?_, ?_⟩
  · rw [harr]
    exact (hprod _ (g.withExponent m').fundamentalBlock_mem_blocks S hS F hF U hU).symm
  · have h1 := (hval S hS F hF).2.2
    change _ = (g.withExponent m').chessboardNorm S F
    rw [h1]
    simp only [SourcesAndGluing.CubicGrid.chessboardNorm, harr]
    rfl
end NormAgreement
end ChessboardTori
end YangMills.Construction
end
