import YangMills.Construction.InfiniteLattice.ChessboardEstimateAndRulesOnMirrorGrids
import YangMills.Construction.InfiniteLattice.MomentsOfTheColumnOverACellProof
import YangMills.Construction.InfiniteLattice.ObjectsOfAMirrorGridOnTheTorus
import YangMills.Construction.InfiniteLattice.TallColumnOverACellIsBoundedCrudely
import YangMills.Construction.SourcesAndGluing.DominationByTheChessboard
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open YangMills.Construction.InfiniteLattice (AmbientSpace timeAxis upperAlgebra observableSupNorm timeReflect)
noncomputable section
namespace YangMills.Construction.MultipleReflections
theorem finprod_eq_prod_image_range {ι R : Type*} [DecidableEq ι] [CommMonoid R]
    {e : ℕ → ι} (he : Function.Injective e) (m : ℕ) (f : ι → R)
    (h : ∀ i, i ∉ (Finset.range m).image e → f i = 1) :
    ∏ᶠ i, f i = ∏ l ∈ Finset.range m, f (e l) := by
  rw [finprod_eq_prod_of_mulSupport_subset (s := (Finset.range m).image e) f, Finset.prod_image]
  · exact fun a _ b _ hab => he hab
  · intro i hi
    by_contra hn
    exact hi (h i hn)
theorem prod_range_add_two {R : Type*} [CommMonoid R] (φ : ℕ → R) (m : ℕ) :
    ∏ l ∈ Finset.range (m + 2), φ l = φ 0 * (∏ l ∈ Finset.range m, φ (l + 1)) * φ (m + 1) := by
  rw [Finset.prod_range_succ, Finset.prod_range_succ', mul_comm (∏ l ∈ Finset.range m, φ (l + 1))]
theorem latticeSymmetry_ext {a : ℝ} {s s' : InfiniteLattice.LatticeSymmetry a}
    (h : s.toFun = s'.toFun) : s = s' := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
namespace Setup.Grid
variable {D : Setup} (G : D.Grid)
def coarsen (k₀ : ℕ) (w : Fin 4 → ℤ) : D.Grid where
  edge := (D.L : ℝ) ^ k₀ * G.edge
  edge_admissible := G.edge_admissible.pow_mul D.isAdmissible k₀
  shift := G.cornerAt w
  shift_mem μ := by
    obtain ⟨i, hi⟩ := G.shift_mem μ
    obtain ⟨N, hN⟩ := InfiniteLattice.ReflectionGrid.exists_edge_eq_natCast_mul_spacingAt G D.isAdmissible
    refine ⟨i + w μ * N, ?_⟩
    simp only [InfiniteLattice.ReflectionGrid.cornerAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hi, hN]
    push_cast
    ring
theorem isWall_coarsen (k₀ : ℕ) (w : Fin 4 → ℤ) (α : Fin 4) (n : ℤ) :
    G.IsWall ((G.coarsen k₀ w).wall α n) := by
  refine ⟨α, w α + n * ((D.L ^ k₀ : ℕ) : ℤ), ?_⟩
  ext x
  change x α = G.cornerAt w α + n * ((D.L : ℝ) ^ k₀ * G.edge) ↔ x α = G.shift α + _ * G.edge
  simp only [InfiniteLattice.ReflectionGrid.cornerAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  constructor <;> intro h <;> rw [h] <;> ring
def timeIndex (l : ℤ) : Fin 4 → ℤ := Pi.single timeAxis l
theorem timeIndex_injective : Function.Injective timeIndex := by
  intro l l' h
  have := congrFun h timeAxis
  simpa [timeIndex] using this
def centringCorner (k : Fin 4 → ℤ) (M : ℕ) : Fin 4 → ℤ :=
  fun α => if α = timeAxis then k α else k α - M
variable (k : Fin 4 → ℤ)
theorem shift_coarsen_timeAxis (k₀ M : ℕ) :
    (G.coarsen k₀ (centringCorner k M)).shift timeAxis = G.baseTime k := by
  rw [baseTime_eq]
  simp [coarsen, InfiniteLattice.ReflectionGrid.cornerAt, centringCorner, mul_comm]
theorem tile_subset_coarsen {k₀ M : ℕ} (hM : D.L ^ k₀ = 2 * M + 1) (l i : ℤ)
    (h₁ : l * ((D.L ^ k₀ : ℕ) : ℤ) + 1 ≤ i) (h₂ : i ≤ (l + 1) * ((D.L ^ k₀ : ℕ) : ℤ)) :
    G.tile (stackIndex k i) ⊆ (G.coarsen k₀ (centringCorner k M)).tile (timeIndex l) := by
  have hs := G.edge_pos
  have hN : (D.L : ℝ) ^ k₀ = 2 * (M : ℝ) + 1 := by exact_mod_cast hM
  have h₁' : (l : ℝ) * (2 * (M : ℝ) + 1) + 1 ≤ i := by
    have : ((l * ((D.L ^ k₀ : ℕ) : ℤ) + 1 : ℤ) : ℝ) ≤ i := by exact_mod_cast h₁
    push_cast at this
    rwa [hN] at this
  have h₂' : (i : ℝ) ≤ ((l : ℝ) + 1) * (2 * (M : ℝ) + 1) := by
    have : (i : ℝ) ≤ (((l + 1) * ((D.L ^ k₀ : ℕ) : ℤ) : ℤ) : ℝ) := by exact_mod_cast h₂
    push_cast at this
    rwa [hN] at this
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  intro x hx μ
  have hxμ : G.cornerAt (stackIndex k i) μ ≤ x μ ∧ x μ ≤ G.cornerAt (stackIndex k i) μ + G.edge := hx μ
  change (G.coarsen k₀ (centringCorner k M)).cornerAt (timeIndex l) μ ≤ x μ ∧
    x μ ≤ (G.coarsen k₀ (centringCorner k M)).cornerAt (timeIndex l) μ +
      (G.coarsen k₀ (centringCorner k M)).edge
  have hside : (G.coarsen k₀ (centringCorner k M)).edge = (2 * (M : ℝ) + 1) * G.edge := by
    rw [← hN]; rfl
  have hc : (G.coarsen k₀ (centringCorner k M)).cornerAt (timeIndex l) μ =
      G.shift μ + G.edge * (centringCorner k M μ : ℝ) +
        (2 * (M : ℝ) + 1) * G.edge * (timeIndex l μ : ℝ) := by
    rw [← hside]
    simp [InfiniteLattice.ReflectionGrid.cornerAt, coarsen]
  rw [hc, hside]
  by_cases h : μ = timeAxis
  · subst h
    simp only [InfiniteLattice.ReflectionGrid.cornerAt, stackIndex, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      timeIndex, centringCorner, Pi.single_eq_same, if_true] at hxμ ⊢
    push_cast at hxμ ⊢
    simp only [mul_one] at hxμ
    have e1 := mul_nonneg hs.le (sub_nonneg.2 h₁')
    have e2 := mul_nonneg hs.le (sub_nonneg.2 h₂')
    constructor <;> nlinarith [hxμ.1, hxμ.2]
  · simp only [InfiniteLattice.ReflectionGrid.cornerAt, stackIndex, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      timeIndex, centringCorner, Pi.single_eq_of_ne h, if_neg h] at hxμ ⊢
    push_cast at hxμ ⊢
    simp only [mul_zero, add_zero] at hxμ ⊢
    have e1 := mul_nonneg hs.le hM0
    constructor <;> nlinarith [hxμ.1, hxμ.2]
theorem sum_sub_timeIndex (l l' : ℤ) : ∑ α, (timeIndex l' α - timeIndex l α) = l' - l := by
  simp [timeIndex, Finset.sum_sub_distrib]
theorem stackReflect_eq_reflectedCopy (G' : D.Grid) (h : G'.shift timeAxis = G.baseTime k)
    (X : D.GaugeField → ℂ) :
    G.stackReflect k 0 X = G'.reflectedCopy (timeIndex 0) (timeIndex (-1)) X := by
  have hiso : G'.tileSymmetry (timeIndex 0) (timeIndex (-1)) =
      timeReflect (G.wallTimeHalf k 0) := by
    apply latticeSymmetry_ext
    funext x α
    rw [InfiniteLattice.timeReflect_apply, G.wallTimeHalf_zero k]
    change G'.tileReflection _ _ x α = _
    by_cases hα : α = timeAxis
    · subst hα
      have hodd : ¬ Even (timeIndex (-1) timeAxis - timeIndex 0 timeAxis) := by
        simp [timeIndex]
      simp only [tileReflection, if_neg hodd, h]
      simp [timeIndex]
      ring
    · simp [tileReflection, timeIndex, Pi.single_eq_of_ne hα]
  have hs : tileSign (timeIndex 0) (timeIndex (-1)) = -1 := by
    rw [tileSign, sum_sub_timeIndex]
    decide
  funext U
  simp only [reflectedCopy, stackReflect, hs, hiso, Conventions.signedConjFun, Conventions.signedConj]
  rw [if_neg (by decide)]
theorem stackShift_actOn_eq_reflectedCopy (G' : D.Grid) (i m : ℤ) (h : (i : ℝ) * G.edge = 2 * m * G'.edge)
    (X : D.GaugeField → ℂ) :
    (G.stackShift i).actOn X = G'.reflectedCopy (timeIndex 0) (timeIndex (2 * m)) X := by
  have hiso : G'.tileSymmetry (timeIndex 0) (timeIndex (2 * m)) = G.stackShift i := by
    apply latticeSymmetry_ext
    funext x α
    rw [G.stackShift_apply]
    change G'.tileReflection _ _ x α = _
    by_cases hα : α = timeAxis
    · subst hα
      have hev : Even (timeIndex (2 * m) timeAxis - timeIndex 0 timeAxis) := by
        simp [timeIndex]
      simp only [tileReflection, if_pos hev]
      simp [timeIndex, h]
    · simp [tileReflection, timeIndex, Pi.single_eq_of_ne hα]
  have hs : tileSign (timeIndex 0) (timeIndex (2 * m)) = 1 := by
    rw [tileSign, sum_sub_timeIndex, sub_zero, zpow_mul]
    simp
  funext U
  simp only [reflectedCopy, hs, hiso, Conventions.signedConjFun, Conventions.signedConj, if_true]
theorem reflectedCopy_mem_and_norm_le (hChess : ChessboardBoundAndRules) (G' : D.Grid)
    (ℓ' : ℝ) (hℓ' : ℓ' ∈ PeriodicLattice.torusSides D.L) (hfit : 2 * G'.edge ≤ ℓ') (p p' : Fin 4 → ℤ)
    (X : D.GaugeField → ℂ) (hX : X ∈ G'.tileAlgebra p) :
    G'.reflectedCopy p p' X ∈ G'.tileAlgebra p' ∧
      G'.chessboardNormAt ℓ' hℓ' p' (G'.reflectedCopy p p' X) ≤ observableSupNorm X := by
  have hs : 2 * G'.edge ≤ (D.atSide ℓ' hℓ').side := by
    rw [Setup.side_atSide]
    exact hfit
  have hall := hChess (D.atSide ℓ' hℓ') G' hs
  have hd := hall.2.2.2.2.2.2.2 0 G' (by simp) hs (fun α n => ⟨α, n, rfl⟩) p' {p'}
    (fun q hq => by rw [Set.mem_singleton_iff.1 hq]) p X hX
  simp only [finprod_mem_singleton, Set.ncard_singleton, pow_one] at hd
  refine ⟨hd.1, hd.2.trans ?_⟩
  exact (hall.2.2.2.2.2.2.1 p p X 1 hX).2.2.1
theorem stackProd_mul_stackProd (F : D.GaugeField → ℂ) {a b c : ℤ} (h₁ : a ≤ b + 1) (h₂ : b ≤ c)
    (U : D.GaugeField) :
    G.stackProd k F a b U * G.stackProd k F (b + 1) c U = G.stackProd k F a c U := by apply _root_.YangMills.Construction.MultipleReflections.StackCorrelations.stackProd_mul_stackProd <;> assumption
theorem prod_blocks_stackProd (F : D.GaugeField → ℂ) (N m : ℕ) (U : D.GaugeField) :
    ∏ l ∈ Finset.range m, G.stackProd k F ((l : ℤ) * N + 1) (((l : ℤ) + 1) * N) U =
      G.stackProd k F 1 ((m : ℤ) * N) U := by
  induction m with
  | zero => simp [stackProd]
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    have h0 : (0 : ℤ) ≤ (m : ℤ) * N := by positivity
    have := G.stackProd_mul_stackProd k F (a := 1) (b := (m : ℤ) * N) (c := ((m : ℤ) + 1) * N)
      (by omega) (by nlinarith) U
    push_cast
    exact this
theorem stackIndex_injective : Function.Injective (stackIndex k) := by
  intro i i' h
  have := congrFun h timeAxis
  simpa [stackIndex] using this
theorem block_mem_and_norm_le (hChess : ChessboardBoundAndRules)
    {F : D.GaugeField → ℂ} (hF : F ∈ G.tileAlgebra k) {k₀ M : ℕ} (hM : D.L ^ k₀ = 2 * M + 1)
    (ℓ' : ℝ) (hℓ' : ℓ' ∈ PeriodicLattice.torusSides D.L)
    (hfit : 2 * (G.coarsen k₀ (centringCorner k M)).edge ≤ ℓ') (l : ℕ) :
    G.stackProd k F ((l : ℤ) * (D.L ^ k₀ : ℕ) + 1) (((l : ℤ) + 1) * (D.L ^ k₀ : ℕ)) ∈
        (G.coarsen k₀ (centringCorner k M)).tileAlgebra (timeIndex l) ∧
      (G.coarsen k₀ (centringCorner k M)).chessboardNormAt ℓ' hℓ' (timeIndex l)
          (G.stackProd k F ((l : ℤ) * (D.L ^ k₀ : ℕ) + 1) (((l : ℤ) + 1) * (D.L ^ k₀ : ℕ))) ≤
        G.chessboardNormAt ℓ' hℓ' k F ^ (D.L ^ k₀) := by
  have hs' : 2 * (G.coarsen k₀ (centringCorner k M)).edge ≤ (D.atSide ℓ' hℓ').side := by
    rw [Setup.side_atSide]
    exact hfit
  have hL1 : (1 : ℝ) ≤ (D.L : ℝ) ^ k₀ := one_le_pow₀ D.one_lt_L.le
  have hsG : 2 * G.edge ≤ (D.atSide ℓ' hℓ').side := by
    refine le_trans ?_ hs'
    have : G.edge ≤ (D.L : ℝ) ^ k₀ * G.edge := le_mul_of_one_le_left G.edge_pos.le hL1
    change 2 * G.edge ≤ 2 * ((D.L : ℝ) ^ k₀ * G.edge)
    linarith
  set a : ℤ := (l : ℤ) * (D.L ^ k₀ : ℕ) + 1 with ha
  set b : ℤ := ((l : ℤ) + 1) * (D.L ^ k₀ : ℕ) with hb
  have hO : ∀ q ∈ stackIndex k '' (↑(Finset.Icc a b) : Set ℤ),
      G.tile q ⊆ (G.coarsen k₀ (centringCorner k M)).tile (timeIndex l) := by
    rintro q ⟨i, hi, rfl⟩
    have hi' := Finset.mem_Icc.1 (Finset.mem_coe.1 hi)
    exact G.tile_subset_coarsen k hM l i hi'.1 hi'.2
  have hd := (hChess (D.atSide ℓ' hℓ') G hsG).2.2.2.2.2.2.2 k₀
    (G.coarsen k₀ (centringCorner k M)) rfl hs' (G.isWall_coarsen k₀ _) (timeIndex l)
    (stackIndex k '' (↑(Finset.Icc a b) : Set ℤ)) hO k F hF
  have hprod : (fun U => ∏ᶠ q ∈ stackIndex k '' (↑(Finset.Icc a b) : Set ℤ), G.reflectedCopy k q F U) =
      G.stackProd k F a b := by
    funext U
    rw [finprod_mem_image (stackIndex_injective k).injOn, finprod_mem_coe_finset]
    rfl
  have hcard : (stackIndex k '' (↑(Finset.Icc a b) : Set ℤ)).ncard = D.L ^ k₀ := by
    rw [Set.ncard_image_of_injective _ (stackIndex_injective k), Set.ncard_coe_finset,
      Int.card_Icc]
    have : b + 1 - a = ((D.L ^ k₀ : ℕ) : ℤ) := by
      rw [ha, hb]
      ring
    rw [this, Int.toNat_natCast]
  have hv := hd.2
  rw [hcard] at hv
  refine ⟨hprod ▸ hd.1, ?_⟩
  rw [← hprod]
  exact hv
theorem exists_coarsen_of_mem_upperAlgebra (A : D.GaugeField → ℂ)
    (hA : A ∈ upperAlgebra (G.wallTimeHalf k 0)) :
    ∃ k₀ M : ℕ, D.L ^ k₀ = 2 * M + 1 ∧
      A ∈ (G.coarsen k₀ (centringCorner k M)).tileAlgebra (timeIndex 0) := by
  obtain ⟨hobs, S, hSH, hSb, hS⟩ :
      InfiniteLattice.IsBoundedlyLocalizedIn
        (InfiniteLattice.halfSpaceAbove (G.wallTimeHalf k 0)) A := hA
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hSb
  have hs := G.edge_pos
  have hL1 := D.one_lt_L
  set p : Fin 4 → ℝ := fun μ => G.shift μ + G.edge * k μ with hp
  set B : ℝ := |R| + ∑ μ, |p μ| with hB
  obtain ⟨k₀, hk⟩ := pow_unbounded_of_one_lt (2 * B / G.edge + 1) hL1
  obtain ⟨M, hM⟩ : Odd (D.L ^ k₀) := D.isAdmissible.1.pow
  refine ⟨k₀, M, hM, ?_⟩
  have hNr : (D.L : ℝ) ^ k₀ = 2 * (M : ℝ) + 1 := by exact_mod_cast hM
  have hMl : B < M * G.edge := by
    rw [hNr] at hk
    have h1 : 2 * B / G.edge < 2 * M := by linarith
    rw [div_lt_iff₀ hs] at h1
    linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hsub : S ⊆ (G.coarsen k₀ (centringCorner k M)).tileInterior (timeIndex 0) := by
    intro y hy μ
    have hyμ : |y μ| ≤ R := (norm_le_pi_norm y μ).trans (hR y hy)
    have hpμ : |p μ| ≤ ∑ μ, |p μ| :=
      Finset.single_le_sum (f := fun μ => |p μ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ μ)
    have hRa : R ≤ |R| := le_abs_self R
    have hB' : |R| + |p μ| ≤ B := by rw [hB]; linarith
    have h1 := abs_le.1 hyμ
    have h2 := abs_le.1 (le_refl |p μ|)
    have hside : (G.coarsen k₀ (centringCorner k M)).edge = (2 * (M : ℝ) + 1) * G.edge := by
      rw [← hNr]; rfl
    have hc : (G.coarsen k₀ (centringCorner k M)).cornerAt (timeIndex 0) μ =
        G.shift μ + G.edge * (centringCorner k M μ : ℝ) := by
      simp [InfiniteLattice.ReflectionGrid.cornerAt, coarsen, timeIndex]
    rw [hc, hside]
    by_cases h : μ = timeAxis
    · subst h
      have hyt : (G.wallTimeHalf k 0 : ℝ) < y timeAxis := hSH hy
      rw [G.wallTimeHalf_zero k, baseTime_eq] at hyt
      simp only [centringCorner, if_true]
      have hpt : p timeAxis = G.shift timeAxis + G.edge * k timeAxis := rfl
      constructor
      · linarith [mul_comm G.edge (k timeAxis : ℝ)]
      · nlinarith [h1.2, h2.1, mul_nonneg hM0 hs.le]
    · simp only [centringCorner, if_neg h]
      have hpt : p μ = G.shift μ + G.edge * k μ := rfl
      push_cast
      constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  refine ⟨hobs, ?_⟩
  exact Measurable.mono hS (biSup_mono fun _ hb => ⟨hsub hb.1, hsub hb.2⟩) le_rfl
def scaleAndOrigin : (D.toGluingSetup 0).ScaleAndOrigin where
  scale := G.edge
  scale_eq_zpow := G.isTileEdge_edge.1
  le_scale := G.isTileEdge_edge.2
  origin := G.shift
  origin_ne μ n hn := by
    obtain ⟨p, hp⟩ := G.shift_mem μ
    have ha : (D.toGluingSetup 0).mesh ≠ 0 := (D.toGluingSetup 0).mesh_pos.ne'
    have h1 : (D.toGluingSetup 0).mesh * ((p : ℝ) + 1 / 2) = (D.toGluingSetup 0).mesh * n := hp.symm.trans hn
    have h2 : (p : ℝ) + 1 / 2 = n := mul_left_cancel₀ ha h1
    have h3 : ((2 * p + 1 : ℤ) : ℝ) = ((2 * n : ℤ) : ℝ) := by
      push_cast
      linarith
    have h4 : 2 * p + 1 = 2 * n := by exact_mod_cast h3
    omega
def sideExp (ℓ' : ℝ) (hℓ' : ℓ' ∈ PeriodicLattice.torusSides D.L) : ℕ+ :=
  ⟨hℓ'.choose, hℓ'.choose_spec.1⟩
theorem side_withCutoffAndSide_sideExp (ℓ' : ℝ) (hℓ' : ℓ' ∈ PeriodicLattice.torusSides D.L) :
    ((D.toGluingSetup 0).withCutoffAndSide D.K (sideExp ℓ' hℓ')).side = ℓ' :=
  D.side_atSide ℓ' hℓ'
theorem mem_tileAlgebra_gridAt (hBridge : TorusGridObjectsAgree)
    (ℓ' : ℝ) (hℓ' : ℓ' ∈ PeriodicLattice.torusSides D.L)
    (h : 2 * G.scaleAndOrigin.scale ≤
      ((D.toGluingSetup 0).withCutoffAndSide D.K (sideExp ℓ' hℓ')).side)
    (p : Fin 4 → ℤ) {X : D.GaugeField → ℂ} (hX : X ∈ G.tileAlgebra p) :
    X ∈ (G.scaleAndOrigin.gridAt (sideExp ℓ' hℓ') h).cubeAlgebra p := by
  have hb := ((hBridge (D.atSide ℓ' hℓ') G h).2.2.2.2 0).1
  have hc := hb.2.2.2.2.2 p
  have : X ∈ Setup.Grid.tileObservables (D := D.atSide ℓ' hℓ') G p := hX
  rw [← hc] at this
  exact this
theorem normAt_eq (hBridge : TorusGridObjectsAgree)
    (ℓ' : ℝ) (hℓ' : ℓ' ∈ PeriodicLattice.torusSides D.L) (h : 2 * G.edge ≤ ℓ')
    (p : Fin 4 → ℤ) {X : D.GaugeField → ℂ} (hX : X ∈ G.tileAlgebra p) :
    G.scaleAndOrigin.normAt (sideExp ℓ' hℓ') X = G.chessboardNormAt ℓ' hℓ' p X := by
  have hs : 2 * G.scaleAndOrigin.scale ≤
      ((D.toGluingSetup 0).withCutoffAndSide D.K (sideExp ℓ' hℓ')).side := by
    rw [side_withCutoffAndSide_sideExp]
    exact h
  unfold SourcesAndGluing.GluingSetup.ScaleAndOrigin.normAt
  rw [dif_pos hs]
  exact (((hBridge (D.atSide ℓ' hℓ') G hs).2.2.2.2 0).2.2.2 p X hX).2.2
theorem pnat_monotone_of_le_add_one {u : ℕ+ → ℝ} (h : ∀ j, u j ≤ u (j + 1)) : Monotone u := by
  have hv : Monotone (fun n : ℕ => u n.succPNat) :=
    monotone_nat_of_le_succ fun n => h n.succPNat
  intro a b hab
  have := hv (PNat.natPred_le_natPred.2 hab)
  simpa using this
theorem norm_integral_prod_le_liminf (hChess : ChessboardBoundAndRules)
    (hBridge : TorusGridObjectsAgree)
    (hDom : SourcesAndGluing.ChessboardDomination)
    {μ : Measure D.GaugeField} (hμ : μ ∈ D.gibbsStates)
    (ℓ : ℕ+ → PeriodicLattice.torusSides D.L) (hℓ : D.IncreasesToInfinity ℓ)
    {c : ℕ → Fin 4 → ℤ} (hc : Function.Injective c) (m : ℕ) (g : ℕ → D.GaugeField → ℂ)
    (hg : ∀ l < m, g l ∈ G.tileAlgebra (c l)) :
    ‖∫ U, ∏ l ∈ Finset.range m, g l U ∂μ‖ ≤
      liminf (fun j => ∏ l ∈ Finset.range m,
        G.chessboardNormAt (ℓ j) (ℓ j).2 (c l) (g l)) atTop := by
  classical
  set Fam : (Fin 4 → ℤ) → D.GaugeField → ℂ :=
    fun i => ∏ l ∈ Finset.range m, if c l = i then g l else 1 with hFam
  have hin : ∀ l < m, Fam (c l) = g l := by
    intro l hl
    rw [hFam]
    simp only
    rw [Finset.prod_eq_single l]
    · simp
    · intro b _ hb
      rw [if_neg fun h => hb (hc h)]
    · intro h
      exact absurd (Finset.mem_range.2 hl) h
  have hout : ∀ i, i ∉ (Finset.range m).image c → Fam i = 1 := by
    intro i hi
    refine Finset.prod_eq_one fun l hl => ?_
    rw [if_neg fun h => hi (Finset.mem_image.2 ⟨l, hl, h⟩)]
  have hmem : ∀ i, Fam i ∈ G.tileAlgebra i := by
    intro i
    by_cases hi : i ∈ (Finset.range m).image c
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hi
      rw [hin l (Finset.mem_range.1 hl)]
      exact hg l (Finset.mem_range.1 hl)
    · rw [hout i hi]
      exact one_mem _
  have hfin : (Function.mulSupport Fam).Finite := by
    refine ((Finset.range m).image c).finite_toSet.subset fun i hi => ?_
    by_contra hn
    exact hi (hout i hn)
  set n : ℕ+ → ℕ+ := fun j => sideExp (ℓ j) (ℓ j).2 with hn
  have hside : (fun j => ((D.toGluingSetup 0).withCutoffAndSide D.K (n j)).side) =
      fun j => (ℓ j : ℝ) := by
    funext j
    exact side_withCutoffAndSide_sideExp _ _
  have hdom := (hDom (D.toGluingSetup 0) G.scaleAndOrigin μ hμ n
    (by rw [hside]; exact pnat_monotone_of_le_add_one hℓ.1)
    (by rw [hside]; exact hℓ.2) Fam
    (fun j h i => G.mem_tileAlgebra_gridAt hBridge _ _ h i (hmem i)) hfin).1
  have hint : (fun U => ∏ᶠ i, Fam i U) = fun U => ∏ l ∈ Finset.range m, g l U := by
    funext U
    rw [finprod_eq_prod_image_range hc m (fun i => Fam i U)
      (fun i hi => by simp only [hout i hi, Pi.one_apply])]
    exact Finset.prod_congr rfl fun l hl => by rw [hin l (Finset.mem_range.1 hl)]
  have hfit : ∀ᶠ j in atTop, 2 * G.edge ≤ (ℓ j : ℝ) := hℓ.2.eventually_ge_atTop _
  have hval : (fun j => ∏ᶠ i, G.scaleAndOrigin.normAt (n j) (Fam i)) =ᶠ[atTop]
      fun j => ∏ l ∈ Finset.range m, G.chessboardNormAt (ℓ j) (ℓ j).2 (c l) (g l) := by
    filter_upwards [hfit] with j hj
    rw [finprod_eq_prod_image_range hc m
      (fun i => G.scaleAndOrigin.normAt (n j) (Fam i))]
    · refine Finset.prod_congr rfl fun l hl => ?_
      have hl' := Finset.mem_range.1 hl
      exact (congrArg (G.scaleAndOrigin.normAt (n j)) (hin l hl')).trans
        (G.normAt_eq hBridge _ _ hj _ (hg l hl'))
    · intro i hi
      refine (congrArg (G.scaleAndOrigin.normAt (n j)) (hout i hi)).trans
        ((G.normAt_eq hBridge _ _ hj i (one_mem _)).trans ?_)
      have hs : 2 * G.edge ≤ (D.atSide (ℓ j) (ℓ j).2).side := by
        rw [Setup.side_atSide]
        exact hj
      exact ((hChess (D.atSide (ℓ j) (ℓ j).2) G hs).2.2.2.2.2.2.1 i i 1 1 (one_mem _)).2.1
  have hdom' : ‖∫ U : D.GaugeField, ∏ᶠ i, Fam i U ∂μ‖ ≤
      liminf (fun j => ∏ᶠ i, G.scaleAndOrigin.normAt (n j) (Fam i)) atTop := hdom
  rw [liminf_congr hval, hint] at hdom'
  exact hdom'
end Setup.Grid
theorem tallStackOverTileBoundedCrudely
    (hChess : ChessboardBoundAndRules)
    (hBridge : TorusGridObjectsAgree)
    (hDom : SourcesAndGluing.ChessboardDomination) :
    TallStackOverTileBoundedCrudely := by
  intro D μ hμ G k F hF A hA ℓ hℓ
  obtain ⟨k₀, M, hM, hAc⟩ := G.exists_coarsen_of_mem_upperAlgebra k A hA
  refine ⟨k₀, fun n' _ => ?_⟩
  set G' := G.coarsen k₀ (Setup.Grid.centringCorner k M) with hG'
  set N : ℕ := D.L ^ k₀ with hN
  have hG'side : G'.edge = (N : ℝ) * G.edge := by
    rw [hN]
    push_cast
    rfl
  have hfit : ∀ᶠ j in atTop, 2 * G'.edge ≤ (ℓ j : ℝ) := hℓ.1.2.eventually_ge_atTop _
  obtain ⟨j₀, hj₀⟩ := hfit.exists
  set T₀ : D.GaugeField → ℂ :=
    G'.reflectedCopy (Setup.Grid.timeIndex 0) (Setup.Grid.timeIndex (-1)) A with hT₀
  set T₁ : D.GaugeField → ℂ :=
    G'.reflectedCopy (Setup.Grid.timeIndex 0) (Setup.Grid.timeIndex (2 * (n' : ℤ))) A with hT₁
  have hΘ : G.stackReflect k 0 A = T₀ :=
    G.stackReflect_eq_reflectedCopy k G' (G.shift_coarsen_timeAxis k k₀ M) A
  have hτ : (G.stackShift (2 * ((N * n' : ℕ) : ℤ))).actOn A = T₁ := by
    refine G.stackShift_actOn_eq_reflectedCopy G' _ _ ?_ A
    rw [hG'side]
    push_cast
    ring
  set E : ℕ → D.GaugeField → ℂ :=
    fun l => G.stackProd k F ((l : ℤ) * (N : ℕ) + 1) (((l : ℤ) + 1) * (N : ℕ)) with hE
  set g : ℕ → D.GaugeField → ℂ :=
    fun l => if l = 0 then T₀ else if l = 2 * n' + 1 then T₁ else E (l - 1) with hg
  set c : ℕ → Fin 4 → ℤ := fun l => Setup.Grid.timeIndex ((l : ℤ) - 1) with hc
  have hcinj : Function.Injective c := by
    intro l l' h
    have := Setup.Grid.timeIndex_injective h
    omega
  have hg0 : g 0 = T₀ := by simp [hg]
  have hg1 : g (2 * n' + 1) = T₁ := by simp [hg]
  have hgE : ∀ l < 2 * n', g (l + 1) = E l := by
    intro l hl
    have h : l ≠ 2 * n' := by omega
    simp [hg, h]
  have hc0 : c 0 = Setup.Grid.timeIndex (-1) := by simp [hc]
  have hc1 : c (2 * n' + 1) = Setup.Grid.timeIndex (2 * (n' : ℤ)) := by
    simp only [hc]
    congr 1
    push_cast
    ring
  have hcE : ∀ l : ℕ, c (l + 1) = Setup.Grid.timeIndex (l : ℤ) := by
    intro l
    simp only [hc]
    congr 1
    push_cast
    ring
  have hT₀v : ∀ j, 2 * G'.edge ≤ (ℓ j : ℝ) →
      G'.chessboardNormAt (ℓ j) (ℓ j).2 (c 0) (g 0) ≤ observableSupNorm A := by
    intro j hj
    rw [hc0, hg0]
    exact (Setup.Grid.reflectedCopy_mem_and_norm_le hChess G' _ (ℓ j).2 hj _ _ A hAc).2
  have hT₁v : ∀ j, 2 * G'.edge ≤ (ℓ j : ℝ) →
      G'.chessboardNormAt (ℓ j) (ℓ j).2 (c (2 * n' + 1)) (g (2 * n' + 1)) ≤
        observableSupNorm A := by
    intro j hj
    rw [hc1, hg1]
    exact (Setup.Grid.reflectedCopy_mem_and_norm_le hChess G' _ (ℓ j).2 hj _ _ A hAc).2
  have hEv : ∀ j, 2 * G'.edge ≤ (ℓ j : ℝ) → ∀ l < 2 * n',
      G'.chessboardNormAt (ℓ j) (ℓ j).2 (c (l + 1)) (g (l + 1)) ≤
        G.chessboardNormAt (ℓ j) (ℓ j).2 k F ^ N := by
    intro j hj l hl
    rw [hcE, hgE l hl]
    exact (G.block_mem_and_norm_le k hChess hF hM _ (ℓ j).2 hj l).2
  have hmem : ∀ l < 2 * n' + 2, g l ∈ G'.tileAlgebra (c l) := by
    intro l hl
    rcases Nat.eq_zero_or_pos l with rfl | hpos
    · rw [hc0, hg0]
      exact (Setup.Grid.reflectedCopy_mem_and_norm_le hChess G' _ (ℓ j₀).2 hj₀ _ _ A hAc).1
    · by_cases hlast : l = 2 * n' + 1
      · subst hlast
        rw [hc1, hg1]
        exact (Setup.Grid.reflectedCopy_mem_and_norm_le hChess G' _ (ℓ j₀).2 hj₀ _ _ A hAc).1
      · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
        rw [hcE, hgE l' (by omega)]
        exact (G.block_mem_and_norm_le k hChess hF hM _ (ℓ j₀).2 hj₀ l').1
  have hint : G.stackCorrelation k μ F A (N * n') = ∫ U, ∏ l ∈ Finset.range (2 * n' + 2), g l U ∂μ := by
    unfold Setup.Grid.stackCorrelation
    refine integral_congr_ae (Eventually.of_forall fun U => ?_)
    change _ = ∏ l ∈ Finset.range (2 * n' + 2), g l U
    rw [prod_range_add_two, hg0, hg1, hΘ, hτ]
    have hst : ∏ l ∈ Finset.range (2 * n'), g (l + 1) U =
        G.stackProd k F 1 (2 * ((N * n' : ℕ) : ℤ)) U := by
      rw [Finset.prod_congr rfl fun l hl => by rw [hgE l (Finset.mem_range.1 hl)]]
      have := G.prod_blocks_stackProd k F N (2 * n') U
      have e : (((2 * n' : ℕ) : ℤ)) * (N : ℤ) = 2 * ((N * n' : ℕ) : ℤ) := by
        push_cast
        ring
      rw [e] at this
      exact this
    rw [hst]
  set x : ℕ+ → ℝ := fun j => G.chessboardNormAt (ℓ j) (ℓ j).2 k F with hx
  have hxnn : ∀ j, 0 ≤ x j := fun j => Real.rpow_nonneg (norm_nonneg _) _
  have hvnn : ∀ j l, 0 ≤ G'.chessboardNormAt (ℓ j) (ℓ j).2 (c l) (g l) :=
    fun j l => Real.rpow_nonneg (norm_nonneg _) _
  set C : ℝ := observableSupNorm A ^ 2 with hC
  have hprod : ∀ j, 2 * G'.edge ≤ (ℓ j : ℝ) →
      ∏ l ∈ Finset.range (2 * n' + 2), G'.chessboardNormAt (ℓ j) (ℓ j).2 (c l) (g l) ≤
        C * x j ^ (2 * (N * n')) := by
    intro j hj
    rw [prod_range_add_two]
    have hA0 : 0 ≤ observableSupNorm A := (hvnn j 0).trans (hT₀v j hj)
    have hmid : ∏ l ∈ Finset.range (2 * n'),
        G'.chessboardNormAt (ℓ j) (ℓ j).2 (c (l + 1)) (g (l + 1)) ≤ x j ^ (2 * (N * n')) := by
      calc _ ≤ ∏ _l ∈ Finset.range (2 * n'), x j ^ N :=
            Finset.prod_le_prod (fun l _ => hvnn j (l + 1))
              (fun l hl => hEv j hj l (Finset.mem_range.1 hl))
        _ = x j ^ (2 * (N * n')) := by
            rw [Finset.prod_const, Finset.card_range, ← pow_mul]
            congr 1
            ring
    have h1 := mul_le_mul (hT₀v j hj) hmid (Finset.prod_nonneg fun l _ => hvnn j (l + 1)) hA0
    have h2 := mul_le_mul h1 (hT₁v j hj) (hvnn j _) (mul_nonneg hA0 (pow_nonneg (hxnn j) _))
    calc _ ≤ _ := h2
      _ = C * x j ^ (2 * (N * n')) := by
          rw [hC]
          ring
  have hlim := G'.norm_integral_prod_le_liminf hChess hBridge hDom hμ ℓ hℓ.1 hcinj (2 * n' + 2) g hmem
  rw [← hint] at hlim
  refine hlim.trans ?_
  set P : ℕ := 2 * (N * n') with hP
  have hC0 : 0 ≤ C := sq_nonneg _
  set f : ℝ → ℝ := fun y => C * max y 0 ^ P with hf
  have hfmono : Monotone f := fun y y' h =>
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right 0 h) _) hC0
  have hfcont : Continuous f := by fun_prop
  have hxb : ∀ j, x j ≤ observableSupNorm F := by
    intro j
    have hsj : 2 * G.edge ≤ (D.atSide (ℓ j) (ℓ j).2).side := by
      rw [Setup.side_atSide]
      exact hℓ.2 j
    exact ((hChess (D.atSide (ℓ j) (ℓ j).2) G hsj).2.2.2.2.2.2.1 k k F 1 hF).2.2.1
  have hbu : IsBoundedUnder (· ≤ ·) atTop x := isBoundedUnder_of ⟨_, hxb⟩
  have hbl : IsBoundedUnder (· ≥ ·) atTop x := isBoundedUnder_of ⟨0, hxnn⟩
  have hfx : ∀ j, f (x j) = C * x j ^ P := fun j => by
    simp only [hf, max_eq_left (hxnn j)]
  have hmap : f (limsup x atTop) = limsup (f ∘ x) atTop :=
    hfmono.map_limsup_of_continuousAt x hfcont.continuousAt hbu hbl.isCoboundedUnder_le
  have hq0 : 0 ≤ limsup x atTop :=
    le_limsup_of_frequently_le (Frequently.of_forall hxnn) hbu
  have hfu : IsBoundedUnder (· ≤ ·) atTop (f ∘ x) :=
    isBoundedUnder_of ⟨f (observableSupNorm F), fun j => hfmono (hxb j)⟩
  have hfl : IsBoundedUnder (· ≥ ·) atTop (f ∘ x) :=
    isBoundedUnder_of ⟨0, fun j => by
      change 0 ≤ f (x j)
      rw [hfx]
      exact mul_nonneg hC0 (pow_nonneg (hxnn j) _)⟩
  have hau : IsBoundedUnder (· ≥ ·) atTop (fun j =>
      ∏ l ∈ Finset.range (2 * n' + 2), G'.chessboardNormAt (ℓ j) (ℓ j).2 (c l) (g l)) :=
    isBoundedUnder_of ⟨0, fun j => Finset.prod_nonneg fun l _ => hvnn j l⟩
  have hle : ∀ᶠ j in atTop,
      ∏ l ∈ Finset.range (2 * n' + 2), G'.chessboardNormAt (ℓ j) (ℓ j).2 (c l) (g l) ≤
        (f ∘ x) j := by
    filter_upwards [hfit] with j hj
    change _ ≤ f (x j)
    rw [hfx]
    exact hprod j hj
  calc _ ≤ liminf (f ∘ x) atTop := liminf_le_liminf hle hau hfu.isCoboundedUnder_ge
    _ ≤ limsup (f ∘ x) atTop := liminf_le_limsup hfu hfl
    _ = f (limsup x atTop) := hmap.symm
    _ = C * G.limsupStackNorm k ℓ F ^ P := by
        simp only [hf, max_eq_left hq0]
        rfl
end YangMills.Construction.MultipleReflections
end
