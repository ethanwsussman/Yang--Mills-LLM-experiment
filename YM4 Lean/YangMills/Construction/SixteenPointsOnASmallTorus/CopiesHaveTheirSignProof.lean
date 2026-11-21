import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.InequalityOnMirroredCopies.ArrayFallsWithThePeriods
import YangMills.Construction.InequalityOnMirroredCopies.ObservableOffTheFacesIsInTheCell
import YangMills.Construction.SixteenPointsOnASmallTorus.ArrayMeanIsTheMeanOfTheCopies
import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesAboutASite
import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesHaveTheirSign
import YangMills.Construction.Torus.SeparatedTuplesFormsAndDistinctPointsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
private theorem reflectedProductMean_congr_copies {c c' : ℕ} [NeZero c] [NeZero c'] (hc : c = c') (β a₀ : ℝ) (M : ℕ) [NeZero M]
    (φ : TestFunctions.EuclideanFourSpace → ℝ) (t : ℝ) :
    reflectedProductMean β a₀ M c 0 φ t = reflectedProductMean β a₀ M c' 0 φ t := by
  subst hc
  rfl
private theorem dist_toLp_eq (x y : Fin 4 → ℝ) :
    dist (WithLp.toLp 2 x : TestFunctions.EuclideanFourSpace) (WithLp.toLp 2 y) = TorusMetric.euclidNormVec (x - y) := by apply _root_.YangMills.Construction.AmbientPoints.dist_toLp_eq_euclidNormVec <;> assumption
private theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem reflectedMeanNonneg_of (hTrans : reflectedMeanTranslationStatement)
    (hFalls : ReflectedCopies.TiledIntegralFallsWithPeriods)
    (hMean : tiledMeanEqReflectedMeanStatement) (hSmeared : ReflectedCopies.SmearedMemCellObservables) :
    reflectedMeanNonnegStatement := by
  intro ℓ hadm β K κ ρ H Λ φ t z hβ hK hκ hρ hρl hsrc
  rw [hTrans]
  have hblock : Conventions.IsAdmissibleBlockingFactor ℓ.side := ⟨hadm.L_odd, by have := hadm.L_ge; omega⟩
  have hside_pos : (0 : ℝ) < ℓ.side := by
    have := hadm.L_ge
    exact_mod_cast (by omega : 0 < ℓ.side)
  let S : ChessboardTori.ChessboardSetup := ⟨⟨ℓ.side, hblock, ⟨K, hK⟩, 1⟩, β, hβ⟩
  have hSmesh : S.mesh = levelSpacing ℓ.side K 0 := by
    show PeriodicLattice.meshSize ℓ.side K = _
    simp [PeriodicLattice.meshSize, levelSpacing]
  obtain ⟨n, hn⟩ := hadm.L_odd.pow (n := κ)
  have hnR : (ℓ.side : ℝ) ^ κ = 2 * n + 1 := by exact_mod_cast hn
  set s := cellLength ℓ.side K κ with hs
  have hmesh_pos : 0 < levelSpacing ℓ.side K 0 := by
    unfold levelSpacing
    positivity
  have hs_eq : s = (2 * n + 1) * levelSpacing ℓ.side K 0 := by
    rw [hs]
    unfold cellLength
    rw [hnR]
  let G : ChessboardTori.ReflectionGrid S :=
    { q := (κ : ℤ) - (K : ℤ)
      one_sub_K_le_q := by
        show 1 - (K : ℤ) ≤ (κ : ℤ) - (K : ℤ)
        omega
      origin := fun _ => -(s / 2)
      origin_mem := fun _ => ⟨-(n : ℤ) - 1, by
        rw [hSmesh, hs_eq]
        push_cast
        ring⟩ }
  have hGside : G.cellSide = s := by
    show (ℓ.side : ℝ) ^ ((κ : ℤ) - (K : ℤ)) = _
    rw [hs]
    unfold cellLength levelSpacing
    rw [sub_eq_add_neg, zpow_add₀ hside_pos.ne', zpow_natCast]
    simp
  have hadmside : G.HasAdmissibleSide := by
    refine ⟨⟨(κ : ℤ) - (K : ℤ), rfl⟩, ?_⟩
    show S.mesh ≤ G.cellSide / (ℓ.side : ℝ) ^ 2
    rw [hSmesh, hGside, hs, le_div_iff₀ (by positivity)]
    unfold cellLength
    have h1 : (ℓ.side : ℝ) ^ 2 ≤ (ℓ.side : ℝ) ^ κ :=
      pow_le_pow_right₀ (by have := hadm.L_ge; exact_mod_cast (by omega : 1 ≤ ℓ.side)) hκ
    nlinarith
  let C : ChessboardTori.GridCell S := ⟨G, hadmside, 0⟩
  have hcentre : ∀ μ, gridCellCentre C μ = 0 := fun μ => by
    show -(s / 2) + G.cellSide * ((0 : ℤ) : ℝ) + G.cellSide / 2 = 0
    rw [hGside]
    push_cast
    ring
  let ψ : InfiniteLattice.AmbientSpace → ℝ := fun x => φ (WithLp.toLp 2 x)
  have hrecentre : recentredAt C ψ = φ := by
    funext x
    show φ (WithLp.toLp 2 fun μ => gridCellCentre C μ + x μ) = φ x
    simp only [hcentre, zero_add]
  have hcoord : ∀ x, ψ x ≠ 0 → ∀ μ, |x μ| + ρ ≤ s / 2 := fun x hx μ => hsrc.away_from_faces _ hx μ
  have hmem : ∀ x, ψ x ≠ 0 → x ∈ C.cell := fun x hx μ => by
    have h1 := hcoord x hx μ
    have h2 := abs_le.mp (show |x μ| ≤ s / 2 by linarith)
    show x μ - (-(s / 2) + G.cellSide * ((0 : ℤ) : ℝ)) ∈ Set.Icc 0 G.cellSide
    rw [hGside]
    push_cast
    constructor <;> linarith [h2.1, h2.2]
  have hsupp : ReflectedCopies.SupportedInCell C ρ ψ :=
    { radius_pos := hρ
      radius_le := by
        show ρ ≤ G.cellSide / 4
        rw [hGside]
        exact hρl
      lipschitz := ⟨Λ, Λ.2, fun x y => by
        have h1 := hsrc.lipschitz.dist_le_mul (WithLp.toLp 2 x) (WithLp.toLp 2 y)
        rw [dist_toLp_eq, Real.dist_eq] at h1
        exact h1⟩
      support_in_ball := by
        obtain ⟨p, hp⟩ := hsrc.exists_ball
        refine ⟨p.ofLp, fun x hx => ?_⟩
        have h1 := hp _ hx
        have hp' : (WithLp.toLp 2 p.ofLp : TestFunctions.EuclideanFourSpace) = p := rfl
        rw [← hp', dist_toLp_eq] at h1
        exact h1
      support_in_cell := hmem
      far_from_walls := fun x hx w hw => by
        simp only [ChessboardTori.ReflectionGrid.walls, Set.mem_iUnion] at hw
        obtain ⟨μ, k, hk⟩ := hw
        have hk' : w μ = -(s / 2) + k * G.cellSide := hk
        rw [hGside] at hk'
        have h1 := hcoord x hx μ
        have h2 := abs_le.mp (show |x μ| ≤ s / 2 - ρ by linarith)
        refine le_trans ?_ (abs_apply_le_euclidNormVec (x - w) μ)
        rw [Pi.sub_apply, hk']
        rcases le_or_gt k 0 with hk0 | hk0
        · have h3 : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
          refine le_trans ?_ (le_abs_self _)
          nlinarith [h2.1]
        · have h3 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
          refine le_trans ?_ (neg_le_abs _)
          nlinarith [h2.2] }
  have hinterior : ∀ x, ψ x ≠ 0 → x ∈ interior C.cell := fun x hx => by
    refine mem_interior.mpr ⟨⋂ μ : Fin 4, (fun v : InfiniteLattice.AmbientSpace => v μ) ⁻¹' Set.Ioo (-(s / 2)) (s / 2), ?_, ?_, ?_⟩
    · intro v hv μ
      have h1 := Set.mem_iInter.mp hv μ
      show v μ - (-(s / 2) + G.cellSide * ((0 : ℤ) : ℝ)) ∈ Set.Icc 0 G.cellSide
      rw [hGside]
      push_cast
      constructor <;> linarith [h1.1, h1.2]
    · exact isOpen_iInter_of_finite fun μ => isOpen_Ioo.preimage (continuous_apply μ)
    · refine Set.mem_iInter.mpr fun μ => ?_
      have h1 := hcoord x hx μ
      have h2 := abs_lt.mp (show |x μ| < s / 2 by linarith)
      exact h2
  have hcellObs : ReflectedCopies.centredSmeared S ψ t ∈ ChessboardTori.ReflectionGrid.cellObservables (D := S) C.cell := by
    obtain ⟨F, hFm, ⟨B, hB⟩, hFeq⟩ := hSmeared S C ρ ψ hsupp
    refine ⟨fun u => F u - (t : ℂ), hFm.sub_const _, ⟨B + |t|, fun u => ?_⟩, ?_⟩
    · refine (norm_sub_le _ _).trans ?_
      have := hB u
      simpa using this
    · funext U
      show ReflectionsAndOneInsertion.complexSmeared S ψ U - (t : ℂ) = _
      rw [hFeq]
      rfl
  have hfalls := hFalls S G hadmside C.cell C.cell_mem_cellSet _ hcellObs (ReflectedCopies.minimalCounts S)
  have hmean := hMean ℓ.side S C κ 0 ψ t 0 rfl (by show (κ : ℤ) = (κ : ℤ) - (K : ℤ) + (K : ℤ); ring) hinterior
    (fun μ => ⟨0, by simp, by rw [hcentre]; simp⟩)
  rw [hrecentre] at hmean
  have htwo : twoCellSide ℓ.side 0 0 = 2 := by simp [twoCellSide]
  have hre : reflectedProductMean β (levelSpacing ℓ.side K 0) (ℓ.side ^ κ) 2 0 φ t =
      (ReflectedCopies.tiledMean C.grid (ReflectedCopies.cubicCounts S 0) C.cell (ReflectedCopies.centredSmeared S ψ t)).re := by
    rw [hmean, Complex.ofReal_re, ← hSmesh]
    exact (reflectedProductMean_congr_copies htwo β S.mesh (ℓ.side ^ κ) φ t).symm
  rw [hre]
  unfold ReflectedCopies.tiledMean
  rw [Complex.div_ofReal_re]
  exact div_nonneg hfalls.2.1 (integral_nonneg fun _ => (Real.exp_pos _).le)
end YangMills.Construction.SmallTorusCopies
end
