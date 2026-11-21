import YangMills.Construction.SourcesAndGluing.LatticeIsometriesAndTheirAction
import YangMills.Construction.SystemOfAdmissibleConstants.CentredMomentsInTheFineCaseProof
import YangMills.Construction.InfiniteLattice.PeriodisationAndThreeIdentitiesOfTheCovering
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import YangMills.Construction.LawInAState.FromSixteenCopiesToOneBoxProof
import YangMills.Construction.LawInAState.HatsSumToTheFreeKernelProof
import YangMills.Construction.SystemOfAdmissibleConstants.MeansAndValuesOfACellFunction
import YangMills.Construction.SystemOfAdmissibleConstants.OneGridForEveryPiece
import YangMills.Construction.SystemOfAdmissibleConstants.OneProductOfPieces
import YangMills.Construction.SystemOfAdmissibleConstants.ProductOverDistinctCells
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory TestFunctions
namespace AdmissibleConstants
open ChessboardTori ReflectedCopies
open InfiniteLattice (AmbientSpace periodicGibbsSet smearedEnergy)
namespace CenteredProductAux
private lemma abs_coord_le_euclidNormVec (w : AmbientSpace) (μ : Fin 4) :
    |w μ| ≤ TorusMetric.euclidNormVec w := by apply _root_.YangMills.SharedProofs.p10398 <;> assumption
private lemma euclidNormVec_le_of_abs_coord_le {w : AmbientSpace} {r : ℝ} (hr : 0 ≤ r)
    (hw : ∀ μ, |w μ| ≤ r) : TorusMetric.euclidNormVec w ≤ 2 * r := by apply _root_.YangMills.SharedProofs.p16936 <;> assumption
private lemma torusEuclidNorm_torusProj_le_self (S : ℝ) (w : AmbientSpace) :
    TorusMetric.torusEuclidNorm (TorusMetric.torusProj S w) ≤ TorusMetric.euclidNormVec w := by apply _root_.YangMills.Construction.SourcesAndGluing.torusEuclidNorm_torusProj_le <;> assumption
private lemma torusProj_sub (S : ℝ) (x y : AmbientSpace) :
    TorusMetric.torusProj S x - TorusMetric.torusProj S y = TorusMetric.torusProj S (x - y) := by apply _root_.YangMills.DeltaSharedProofs.p500829 <;> assumption
private lemma ofReal_finsum {ι : Type*} (f : ι → ℝ) :
    ((∑ᶠ i, f i : ℝ) : ℂ) = ∑ᶠ i, ((f i : ℝ) : ℂ) := by
  by_cases hf : (Function.support f).Finite
  · exact (Complex.ofRealHom : ℝ →+* ℂ).toAddMonoidHom.map_finsum hf
  · have hf' : ¬ (Function.support fun i => ((f i : ℝ) : ℂ)).Finite := by
      have hsupp : (Function.support fun i => ((f i : ℝ) : ℂ)) = Function.support f := by
        ext i
        simp
      rwa [hsupp]
    rw [finsum_of_infinite_support hf, finsum_of_infinite_support hf']
    simp
private lemma smearedEnergy_ofReal {a : ℝ} (φ : AmbientSpace → ℝ) (W : InfiniteLattice.GaugeField a) :
    smearedEnergy (fun x => (φ x : ℂ)) W = ((smearedEnergy φ W : ℝ) : ℂ) := by
  unfold smearedEnergy
  rw [ofReal_finsum]
  refine finsum_congr fun p => ?_
  simp
abbrev _root_.YangMills.SharedProofs.p95543 := @smearedEnergy_ofReal
private lemma periodize_ofReal (ℓ : ℝ) (φ : AmbientSpace → ℝ) (x : TorusMetric.Torus4 ℓ) :
    periodize ℓ (fun y => (φ y : ℂ)) x = ((periodize ℓ φ x : ℝ) : ℂ) := by
  simp only [periodize, periodicSum]
  exact (Complex.ofReal_tsum _).symm
private lemma smearedObservable_periodize_ofReal {L m : ℕ} {j : ℤ} (φ : AmbientSpace → ℝ)
    (U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) :
    PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide L m) fun y => (φ y : ℂ)) U =
      ((PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide L m) φ) U : ℝ) : ℂ) := by
  unfold PeriodicLattice.smearedObservable
  rw [ofReal_finsum]
  refine finsum_congr fun p => ?_
  rw [periodize_ofReal]
  simp
abbrev _root_.YangMills.SharedProofs.p19060 := @smearedObservable_periodize_ofReal
private lemma smearedEnergy_liftField (hCov : PeriodizationIdentities.Statement)
    (D : ChessboardSetup) (m' : ℕ+) {φ : AmbientSpace → ℝ}
    (hφ : InfiniteLattice.IsBoundedBorelCompactlySupported φ)
    {U : PeriodicLattice.Bond D.L m' ((D.K : ℕ) : ℤ) → Matrices.ComplexMatrix2}
    (hU : U ∈ PeriodicLattice.compactGaugeFields D.L m' ((D.K : ℕ) : ℤ)) :
    smearedEnergy φ ((D.withExponent m').liftField U) =
      PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide D.L m') φ) U := by
  have hφc : InfiniteLattice.IsBoundedBorelCompactlySupported (fun x => (φ x : ℂ)) := by
    obtain ⟨hm, ⟨C, hC⟩, hc⟩ := hφ
    exact ⟨Complex.measurable_ofReal.comp hm, ⟨C, fun x => by simpa using hC x⟩,
      hc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)⟩
  have hid := (hCov D.L m' D.K D.isAdmissible m'.pos D.K.pos D.β D.beta_pos).2.1 _ hφc
    (⟨U, hU⟩ : PeriodicLattice.CompactGaugeField D.L m' ((D.K : ℕ) : ℤ))
  have hcast : ((smearedEnergy φ ((D.withExponent m').liftField U) : ℝ) : ℂ) =
      ((PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide D.L m') φ) U : ℝ) : ℂ) := by
    rw [← smearedObservable_periodize_ofReal, ← smearedEnergy_ofReal]
    exact hid
  exact Complex.ofReal_injective hcast
private lemma torusAverage_eq_integral (D : ChessboardSetup) (m' : ℕ+) (F : D.GaugeField → ℂ) :
    torusAverage D m' F = ∫ U, F ((D.withExponent m').liftField U)
      ∂PeriodicLattice.wilsonGibbsMeasure D.L m' D.K D.β :=
  rfl
private lemma ae_mem_compactGaugeFields (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (D : ChessboardSetup) (m' : ℕ+) :
    ∀ᵐ U ∂PeriodicLattice.wilsonGibbsMeasure D.L m' D.K D.β,
      U ∈ PeriodicLattice.compactGaugeFields D.L m' ((D.K : ℕ) : ℤ) := by
  have hL : 1 < D.L := by
    have := D.isAdmissible.2
    omega
  obtain ⟨-, -, -, -, -, -, -, -, hnull, -⟩ := hW D.L m' D.K D.β hL m'.pos D.K.pos
  exact ae_iff.2 hnull
private lemma copyBound_nonneg {A b l ϱ : ℝ} (hA : 0 ≤ A) (φ : AmbientSpace → ℝ) :
    0 ≤ copyBound A b l ϱ φ := by
  refine mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) (le_max_of_le_left ?_)
  exact Real.iSup_nonneg fun _ => norm_nonneg _
private lemma isBoundedBorelCompactlySupported_of_lipschitz {p : AmbientSpace → ℝ} {α : AmbientSpace}
    {ε : ℝ} (hp : IsLipschitzFor euclidDistR4 p) (hc : ∀ x, p x ≠ 0 → ∀ μ, |x μ - α μ| ≤ ε) :
    InfiniteLattice.IsBoundedBorelCompactlySupported p := by
  obtain ⟨C, hC0, hC⟩ := hp
  have hcont : Continuous p := by
    refine (LipschitzWith.of_dist_le_mul (K := ⟨C * 2, by positivity⟩) fun x y => ?_).continuous
    have hxy : euclidDistR4 x y ≤ 2 * dist x y := by
      refine euclidNormVec_le_of_abs_coord_le dist_nonneg fun μ => ?_
      exact (Real.norm_eq_abs _).symm.le.trans ((norm_le_pi_norm (x - y) μ).trans
        (dist_eq_norm x y).symm.le)
    calc dist (p x) (p y) = ‖p x - p y‖ := dist_eq_norm _ _
      _ ≤ C * euclidDistR4 x y := hC x y
      _ ≤ C * (2 * dist x y) := mul_le_mul_of_nonneg_left hxy hC0
      _ = (C * 2) * dist x y := by ring
  have hcs : HasCompactSupport p := by
    refine HasCompactSupport.intro (K := Set.pi Set.univ fun μ => Set.Icc (α μ - ε) (α μ + ε))
      (isCompact_univ_pi fun _ => isCompact_Icc) fun x hx => ?_
    by_contra h0
    refine hx fun μ _ => ?_
    have := abs_le.mp (hc x h0 μ)
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  exact ⟨hcont.measurable, hcs.exists_bound_of_continuous hcont, hcs⟩
end CenteredProductAux
open CenteredProductAux in
theorem centeredProductBound_holds (hOffset : GridOffsetAvoidsPoints)
    (hMeans : CellFunctionMeanBounds)
    (hProd : DistinctCellProductBound)
    (hCov : PeriodizationIdentities.Statement)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) : CenteredProductBound := by
  intro D A b l ε n k hA hb hkn hn hI hlj hmax hε p α hLip hcube hsep
  obtain ⟨j, hlj⟩ := hlj
  have hL1 : (1 : ℝ) < D.L := D.one_lt_factor
  have ha : 0 < D.mesh := D.mesh_pos
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 < l := by
    rw [hlj]
    exact zpow_pos (by linarith) j
  have hε0 : 0 < ε := by
    rw [hε]
    positivity
  have hm1 : 2 ^ 6 * (n : ℝ) ≤ l / D.mesh := (le_max_left _ _).trans hmax
  have hm2 : (D.L : ℝ) ^ 2 ≤ l / D.mesh := (le_max_right _ _).trans hmax
  have hside : D.IsAdmissibleSide ((D.L : ℝ) ^ j) := by
    refine ⟨⟨j, rfl⟩, ?_⟩
    rw [← hlj, le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ ha] at hm2
    linarith
  have hhalf : ∀ _ : Fin 4, ∃ i : ℤ, D.mesh * (1 / 2) = D.mesh * ((i : ℝ) + 1 / 2) :=
    fun _ => ⟨0, by simp⟩
  let g₀ : ReflectionGrid D := D.gridOfSide j hside (fun _ => D.mesh * (1 / 2)) hhalf
  have hg₀ : g₀.cellSide = l := hlj.symm
  have hratio : (0 : ℤ) ≤ g₀.cellRatio := by linarith [g₀.two_le_cellRatio]
  set m : ℕ := g₀.cellRatio.toNat with hm
  have hmr : (m : ℝ) = (g₀.cellRatio : ℝ) := by
    have : ((m : ℤ) : ℝ) = (g₀.cellRatio : ℝ) := by
      rw [hm, Int.toNat_of_nonneg hratio]
    exact_mod_cast this
  have hlm : l = m * D.mesh := by
    rw [hmr, ← g₀.cellSide_eq, hg₀]
  have hmla : l / D.mesh = m := by
    rw [hlm]
    field_simp
  have hcount : (k : ℝ) * (6 * ε / D.mesh + 1) < m := by
    have hkN : (k : ℝ) ≤ n := by exact_mod_cast hkn
    have hm0 : (2 : ℝ) ^ 6 * n ≤ m := by rwa [hmla] at hm1
    have h6 : 6 * ε / D.mesh = 6 * m / (2 ^ 7 * n) := by
      rw [hε, hlm]
      field_simp
    have hterm : 0 ≤ 6 * (m : ℝ) / (2 ^ 7 * n) + 1 := by positivity
    have hNz : (n : ℝ) ≠ 0 := by positivity
    calc (k : ℝ) * (6 * ε / D.mesh + 1) ≤ n * (6 * m / (2 ^ 7 * n) + 1) := by
          rw [h6]
          exact mul_le_mul_of_nonneg_right hkN hterm
      _ = 6 * m / 2 ^ 7 + n := by
          field_simp
      _ < m := by
          have : (0 : ℝ) < m := by nlinarith
          nlinarith
  choose jj hjj using fun μ : Fin 4 => hOffset D.mesh l ε m k ha hε0 hlm hcount fun i => α i μ
  let c : AmbientSpace := fun μ => D.mesh * ((jj μ : ℝ) + 1 / 2)
  let g : ReflectionGrid D := D.gridOfSide j hside c fun μ => ⟨jj μ, rfl⟩
  have hg : g.HasAdmissibleSide := hside
  have hgs : g.cellSide = l := hlj.symm
  have hoff : ∀ μ, g.origin μ = c μ := fun _ => rfl
  let idx : Fin k → Fin 4 → ℤ := fun i μ => ⌊(α i μ - c μ) / l⌋
  have hlow : ∀ i μ, 3 * ε ≤ α i μ - (c μ + l * (idx i μ : ℝ)) := by
    intro i μ
    have h1 := hjj μ i (idx i μ)
    have h2 : l * (idx i μ : ℝ) ≤ α i μ - c μ := by
      have := Int.floor_le ((α i μ - c μ) / l)
      rw [le_div_iff₀ hl] at this
      simpa [idx, mul_comm] using this
    rwa [abs_of_nonneg (by show 0 ≤ α i μ - (c μ + l * (idx i μ : ℝ)); linarith)] at h1
  have hhigh : ∀ i μ, 3 * ε ≤ (c μ + l * ((idx i μ : ℝ) + 1)) - α i μ := by
    intro i μ
    have h1 := hjj μ i (idx i μ + 1)
    have h2 : α i μ - c μ < l * ((idx i μ : ℝ) + 1) := by
      have := Int.lt_floor_add_one ((α i μ - c μ) / l)
      rw [div_lt_iff₀ hl] at this
      simpa [idx, mul_comm] using this
    push_cast at h1
    rwa [abs_of_neg (by show α i μ - (c μ + l * ((idx i μ : ℝ) + 1)) < 0; linarith), neg_sub] at h1
  have hincell : ∀ i x, (∀ μ, |x μ - α i μ| ≤ ε) → x ∈ g.cell (idx i) := by
    intro i x hx μ
    have h1 := abs_le.mp (hx μ)
    have h2 := hlow i μ
    have h3 := hhigh i μ
    rw [hgs, hoff]
    constructor <;> nlinarith
  have hst : ∀ i, SupportedInCell (⟨g, hg, idx i⟩ : GridCell D) (2 * ε) (p i) := by
    intro i
    refine ⟨by positivity, ?_, hLip i, ⟨α i, fun x hx => ?_⟩, fun x hx => hincell i x (hcube i x hx),
      fun x hx z hz => ?_⟩
    · show 2 * ε ≤ g.cellSide / 4
      rw [hgs, hε]
      have h128 : l / (2 ^ 7 * (n : ℝ)) ≤ l / 2 ^ 7 :=
        div_le_div_of_nonneg_left hl.le (by positivity) (by nlinarith)
      have : l / 2 ^ 7 = l / 128 := by norm_num
      linarith
    · exact euclidNormVec_le_of_abs_coord_le hε0.le fun μ => hcube i x hx μ
    · obtain ⟨μ, t, hz⟩ : ∃ μ t, z ∈ g.wall μ t := by
        simpa [ReflectionGrid.walls] using hz
      have hzμ : z μ = c μ + l * (t : ℝ) := by
        have : z μ = g.origin μ + t * g.cellSide := hz
        rw [this, hgs, hoff]
        ring
      have h1 := hjj μ i t
      have h2 := abs_coord_le_euclidNormVec (x - z) μ
      have h3 := abs_le.mp (hcube i x hx μ)
      have h4 : |α i μ - (c μ + l * (t : ℝ))| ≤ |x μ - z μ| + ε := by
        rw [← hzμ]
        have e1 : α i μ - z μ = (x μ - z μ) - (x μ - α i μ) := by ring
        rw [e1]
        exact (abs_sub _ _).trans (add_le_add le_rfl (hcube i x hx μ))
      have h5 : |(x - z) μ| = |x μ - z μ| := rfl
      linarith
  by_cases hz : ∃ i, p i = 0
  · obtain ⟨i, hi⟩ := hz
    have hnn : 0 ≤ ∏ i, 2 * copyBound A b l (2 * ε) (p i) :=
      Finset.prod_nonneg fun i _ => mul_nonneg (by norm_num) (copyBound_nonneg hA _)
    refine ⟨fun ν _ => ?_, fun m' _ _ => ?_⟩
    · have h0 : ∀ U : InfiniteLattice.GaugeField (PeriodicLattice.meshSize D.L ((D.K : ℕ) : ℤ)),
          ∏ i', (smearedEnergy (p i') U - ∫ V, smearedEnergy (p i') V ∂ν) = 0 := by
        intro U
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        simp [hi, smearedEnergy]
      simp only [h0, integral_zero, abs_zero]
      exact hnn
    · have h0 : ∀ U : PeriodicLattice.Bond D.L m' ((D.K : ℕ) : ℤ) → Matrices.ComplexMatrix2,
          ∏ i', (PeriodicLattice.smearedObservable
            (periodize (PeriodicLattice.torusSide D.L m') (p i')) U -
          ∫ V, PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide D.L m') (p i')) V
            ∂PeriodicLattice.wilsonGibbsMeasure D.L m' D.K D.β) = 0 := by
        intro U
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        simp [hi, PeriodicLattice.smearedObservable, periodize, periodicSum]
      simp only [h0, integral_zero, abs_zero]
      exact hnn
  push Not at hz
  have hbb : ∀ i, InfiniteLattice.IsBoundedBorelCompactlySupported (p i) := fun i =>
    isBoundedBorelCompactlySupported_of_lipschitz (hLip i) (hcube i)
  choose pt hpt using fun i => Function.ne_iff.mp (hz i)
  have hdiam : ∀ {x y : AmbientSpace} {t : Fin 4 → ℤ}, x ∈ g.cell t → y ∈ g.cell t →
      euclidDistR4 x y ≤ 2 * l := by
    intro x y t hx hy
    show TorusMetric.euclidNormVec (x - y) ≤ 2 * l
    refine euclidNormVec_le_of_abs_coord_le hl.le fun μ => ?_
    have h1 := hx μ
    have h2 := hy μ
    rw [hgs] at h1 h2
    show |x μ - y μ| ≤ l
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hinj : Function.Injective idx := by
    intro i i' hii
    by_contra hne
    have h1 := hsep i i' hne (pt i) (pt i') (hpt i) (hpt i')
    have hx := hincell i _ (hcube i _ (hpt i))
    have hy := hincell i' _ (hcube i' _ (hpt i'))
    rw [← hii] at hy
    linarith [hdiam hx hy]
  let cd : Fin k → GridCell D := fun i => ⟨g, hg, idx i⟩
  have hsd : ∀ i, (cd i).side = l := fun _ => hgs
  choose κ hκs hκt hκe using fun i => hMeans D A b hA hb hI (cd i) (2 * ε) (p i) (hst i)
  simp only [hsd] at hκs hκt hκe
  have hfam : ∀ e : Fin k → ℝ, (∀ i, |e i - κ i| ≤ copyBound A b l (2 * ε) (p i)) →
      (∀ ν ∈ periodicGibbsSet D.L D.K D.β,
        ‖∫ U, ∏ i, centredSmeared D (p i) (e i) U ∂ν‖ ≤
          ∏ i, 2 * copyBound A b l (2 * ε) (p i)) ∧
      ∀ m' : ℕ+, 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L m' →
        Function.Injective (fun i => (D.withExponent m').proj '' g.cell (idx i)) →
        ‖torusAverage D m' (fun U => ∏ i, centredSmeared D (p i) (e i) U)‖ ≤
          ∏ i, 2 * copyBound A b l (2 * ε) (p i) := by
    intro e he
    exact hProd D g hg k idx hinj (fun i => centredSmeared D (p i) (e i))
      (fun i => 2 * copyBound A b l (2 * ε) (p i)) (fun i => (hκe i (e i) (he i)).1)
      fun i m' hm' => (hκe i (e i) (he i)).2 m' (by rwa [hgs] at hm')
  refine ⟨fun ν hν => ?_, fun m' hm' hap => ?_⟩
  · let e : Fin k → ℝ := fun i => ∫ V, smearedEnergy (p i) V ∂ν
    have h1 := (hfam e fun i => hκs i ν hν).1 ν hν
    have h3 : ∫ U, ∏ i, centredSmeared D (p i) (e i) U ∂ν =
        ((∫ U, ∏ i, (smearedEnergy (p i) U - e i) ∂ν : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (ae_of_all _ fun U => ?_)
      show ∏ i, centredSmeared D (p i) (e i) U =
        ((∏ i, (smearedEnergy (p i) U - e i) : ℝ) : ℂ)
      rw [Complex.ofReal_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Complex.ofReal_sub]
      rfl
    rw [h3, Complex.norm_real, Real.norm_eq_abs] at h1
    exact h1
  · have hobs : ∀ i U, U ∈ PeriodicLattice.compactGaugeFields D.L m' ((D.K : ℕ) : ℤ) →
        smearedEnergy (p i) ((D.withExponent m').liftField U) =
          PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide D.L m') (p i)) U :=
      fun i U hU => smearedEnergy_liftField hCov D m' (hbb i) hU
    let e : Fin k → ℝ := fun i =>
      ∫ V, PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide D.L m') (p i)) V
        ∂PeriodicLattice.wilsonGibbsMeasure D.L m' D.K D.β
    have hmean : ∀ i, torusAverage D m' (ReflectionsAndOneInsertion.complexSmeared D (p i)) =
        (e i : ℂ) := by
      intro i
      rw [torusAverage_eq_integral]
      show _ = ((∫ V, PeriodicLattice.smearedObservable
        (periodize (PeriodicLattice.torusSide D.L m') (p i)) V
        ∂PeriodicLattice.wilsonGibbsMeasure D.L m' D.K D.β : ℝ) : ℂ)
      rw [← integral_complex_ofReal]
      refine integral_congr_ae ((ae_mem_compactGaugeFields hW D m').mono fun U hU => ?_)
      show ((smearedEnergy (p i) ((D.withExponent m').liftField U) : ℝ) : ℂ) = _
      rw [hobs i U hU]
    have he : ∀ i, |e i - κ i| ≤ copyBound A b l (2 * ε) (p i) := by
      intro i
      have h1 := hκt i m' hm'
      rw [hmean, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h1
      exact h1
    have hap' : Function.Injective (fun i => (D.withExponent m').proj '' g.cell (idx i)) := by
      intro i i' hii
      by_contra hne
      have h1 := hap i i' hne (pt i) (pt i') (hpt i) (hpt i')
      have hx := hincell i _ (hcube i _ (hpt i))
      have hz' := hincell i' _ (hcube i' _ (hpt i'))
      have hmem : (D.withExponent m').proj (pt i) ∈
          (D.withExponent m').proj '' g.cell (idx i') := by
        have h2 := Set.mem_image_of_mem (D.withExponent m').proj hx
        have h3 : (D.withExponent m').proj '' g.cell (idx i) =
            (D.withExponent m').proj '' g.cell (idx i') := hii
        rwa [h3] at h2
      obtain ⟨y, hy, hyc⟩ := hmem
      have h2 : TorusMetric.torusProj (PeriodicLattice.torusSide D.L m') (pt i) =
          TorusMetric.torusProj (PeriodicLattice.torusSide D.L m') y := hyc.symm
      rw [h2] at h1
      have h3 : euclidDistTorus (TorusMetric.torusProj (PeriodicLattice.torusSide D.L m') y)
          (TorusMetric.torusProj (PeriodicLattice.torusSide D.L m') (pt i')) ≤ euclidDistR4 y (pt i') := by
        show TorusMetric.torusEuclidNorm (_ - _) ≤ _
        rw [torusProj_sub]
        exact torusEuclidNorm_torusProj_le_self _ _
      linarith [hdiam hy hz']
    have h1 := (hfam e he).2 m' (by rwa [hgs]) hap'
    have h2 : torusAverage D m' (fun U => ∏ i, centredSmeared D (p i) (e i) U) =
        ((∫ U, ∏ i, (PeriodicLattice.smearedObservable
            (periodize (PeriodicLattice.torusSide D.L m') (p i)) U - e i)
          ∂PeriodicLattice.wilsonGibbsMeasure D.L m' D.K D.β : ℝ) : ℂ) := by
      rw [torusAverage_eq_integral, ← integral_complex_ofReal]
      refine integral_congr_ae ((ae_mem_compactGaugeFields hW D m').mono fun U hU => ?_)
      show ∏ i, centredSmeared D (p i) (e i) ((D.withExponent m').liftField U) =
        ((∏ i, (PeriodicLattice.smearedObservable
          (periodize (PeriodicLattice.torusSide D.L m') (p i)) U - e i) : ℝ) : ℂ)
      have h3 : ∀ i, smearedEnergy (p i) ((D.withExponent m').liftField U) =
          PeriodicLattice.smearedObservable (periodize (PeriodicLattice.torusSide D.L m') (p i)) U :=
        fun i => hobs i U hU
      rw [Complex.ofReal_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Complex.ofReal_sub, ← h3 i]
      rfl
    rw [h2, Complex.norm_real, Real.norm_eq_abs] at h1
    exact h1
end AdmissibleConstants
end YangMills.Construction
end
