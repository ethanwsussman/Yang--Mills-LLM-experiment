import YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivityProof
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import YangMills.Construction.MirrorGridsOfEverySide.ChessboardEstimateOnGridsOfEverySide
import YangMills.Construction.MirrorGridsOfEverySide.FactsOfAMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.JensenInequalityFromThePeriodsOfTheState
import YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open MeasureTheory Set
open InfiniteLattice (AmbientSpace)
open ChessboardTori (ReflectionGrid orientationSign)
noncomputable section
namespace MirrorGridsAllSides.JensenBoundFromPeriods
theorem exists_isPeriod (D : GridSetup) {ν : Measure D.GaugeField}
    (hν : ν ∈ D.periodicGibbs) : ∃ p : ℕ, D.IsPeriod ν p := by
  obtain ⟨hG, H, hfin, hinv⟩ := hν
  refine ⟨H.index, hG.1, Nat.one_le_iff_ne_zero.2 hfin.index_ne_zero, ?_⟩
  rintro v ⟨n, hn⟩
  let w : InfiniteLattice.LatticePoint D.mesh := ⟨fun μ => (n μ : ℝ) * D.mesh, n, fun _ => rfl⟩
  have hv : v = H.index • w := by
    apply Subtype.ext
    funext μ
    have : ((H.index • w : InfiniteLattice.LatticePoint D.mesh) : AmbientSpace) μ =
        (H.index : ℝ) * ((n μ : ℝ) * D.mesh) := by
      simp [w]
    rw [this, hn μ]
    ring
  rw [hv]
  exact hinv _ (H.nsmul_index_mem w)
theorem isBoundedObservable_of_mem_cellObservables {D : GridSetup} {S : Set AmbientSpace}
    {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) : InfiniteLattice.IsBoundedObservable F := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.isBoundedObservable_of_mem_cellObservables <;> assumption
theorem exp_mem_cellObservables {D : GridSetup} {S : Set AmbientSpace} {h : D.GaugeField → ℝ}
    (hh : (fun U => (h U : ℂ)) ∈ ReflectionGrid.cellObservables (D := D) S) :
    (fun U => (Real.exp (h U) : ℂ)) ∈ ReflectionGrid.cellObservables (D := D) S := by
  obtain ⟨f, hf, ⟨C, hC⟩, he⟩ := hh
  refine ⟨fun u => (Real.exp (f u).re : ℂ), ?_, ⟨Real.exp C, fun u => ?_⟩, ?_⟩
  · exact Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp (Complex.measurable_re.comp hf))
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 ((Complex.re_le_norm _).trans (hC u))
  · funext U
    have h1 : (h U : ℂ) = f (ReflectionGrid.restrictField S U) := congrFun he U
    have h2 : h U = (f (ReflectionGrid.restrictField S U)).re := by rw [← h1]; simp
    simp only [Function.comp_apply]
    rw [← h2]
theorem finite_latticePoints_cornerCube (D : GridSetup) (c : AmbientSpace) :
    {x : InfiniteLattice.LatticePoint D.mesh | (x : AmbientSpace) ∈ D.cornerCube c}.Finite := by
  have hB : Bornology.IsBounded (D.cornerCube c) := by
    refine (Metric.isBounded_Icc c (fun μ => c μ + D.side)).subset fun x hx => ?_
    exact ⟨fun μ => (hx μ).1, fun μ => (hx μ).2⟩
  obtain ⟨R, hR⟩ := hB.exists_norm_le
  have ha := D.mesh_pos
  let N : ℤ := ⌈R / D.mesh⌉
  let site : (Fin 4 → ℤ) → InfiniteLattice.LatticePoint D.mesh :=
    fun n => ⟨fun μ => (n μ : ℝ) * D.mesh, n, fun _ => rfl⟩
  refine ((Set.finite_Icc (fun _ => -N) fun _ => N).image site).subset ?_
  rintro x hx
  obtain ⟨n, hn⟩ := x.2
  refine ⟨n, ⟨fun μ => ?_, fun μ => ?_⟩, Subtype.ext (funext fun μ => (hn μ).symm)⟩
  all_goals
    have hμ : |(n μ : ℝ) * D.mesh| ≤ R := by
      rw [← hn μ]
      exact (norm_le_pi_norm (x : AmbientSpace) μ).trans (hR _ hx)
    rw [abs_mul, abs_of_pos ha, ← le_div_iff₀ ha] at hμ
    have hN : |(n μ : ℝ)| ≤ (N : ℝ) := hμ.trans (Int.le_ceil _)
    have hN' : |n μ| ≤ N := by exact_mod_cast hN
  · exact (abs_le.mp hN').1
  · exact (abs_le.mp hN').2
theorem coe_cornerCubeLinks (D : GridSetup) (c : AmbientSpace) :
    (D.cornerCubeLinks c : Set D.Link) =
      InfiniteLattice.positiveLinksWithin D.mesh (D.cornerCube c) := by
  refine D.coe_boxLinks ?_
  have hf := finite_latticePoints_cornerCube D c
  refine Set.Finite.of_finite_image (f := fun b : D.Link => (b.initial, b.terminal))
    ((hf.prod hf).subset ?_) ?_
  · rintro _ ⟨b, hb, rfl⟩
    exact ⟨hb.2.1, hb.2.2⟩
  · intro b _ b' _ hbb
    exact InfiniteLattice.Link.ext (congrArg Prod.fst hbb) (congrArg Prod.snd hbb)
theorem mem_cornerCubeLinks_or_opposite_mem (D : GridSetup) (c : AmbientSpace) (b : D.Link)
    (ht : (b.initial : AmbientSpace) ∈ D.cornerCube c) (hd : (b.terminal : AmbientSpace) ∈ D.cornerCube c) :
    b ∈ D.cornerCubeLinks c ∨ b.opposite ∈ D.cornerCubeLinks c := by
  have key : ∀ b' : D.Link, b' ∈ D.cornerCubeLinks c ↔
      b' ∈ InfiniteLattice.positiveLinksWithin D.mesh (D.cornerCube c) := fun b' => by
    rw [← coe_cornerCubeLinks D c]
    rfl
  rw [key, key]
  rcases InfiniteLattice.mem_positiveLinks_or_opposite_mem b with h | h
  · exact Or.inl ⟨h, ht, hd⟩
  · exact Or.inr ⟨h, hd, ht⟩
theorem isBoundedMeasurableInLinks_shift {D : GridSetup} {S : Set AmbientSpace} {c : AmbientSpace}
    (v : InfiniteLattice.LatticePoint D.mesh)
    (hv : ∀ x ∈ interior S, x + (v : AmbientSpace) ∈ D.cornerCube c)
    {F : D.GaugeField → ℂ} (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) :
    D.IsBoundedMeasurableInLinks (D.cornerCubeLinks c)
      ((InfiniteLattice.shift v).actOn F) := by
  classical
  obtain ⟨f, hf, ⟨C, hC⟩, rfl⟩ := hF
  set B := D.cornerCubeLinks c with hBdef
  let tb : D.Link → D.Link := (InfiniteLattice.shift v).linkMap
  let sel : ReflectionGrid.interiorLinks (D := D) S →
      InfiniteLattice.LinkVariables (B : Set D.Link) → Matrices.ComplexMatrix2.specialUnitary := fun b V =>
    if h₁ : tb b.1 ∈ B then V ⟨tb b.1, h₁⟩
    else if h₂ : (tb b.1).opposite ∈ B then (V ⟨(tb b.1).opposite, h₂⟩)⁻¹ else 1
  have hsel : ∀ b, Continuous (sel b) := fun b => by
    by_cases h₁ : tb b.1 ∈ B
    · simp only [sel, dif_pos h₁]
      exact continuous_apply _
    · by_cases h₂ : (tb b.1).opposite ∈ B
      · simp only [sel, dif_neg h₁, dif_pos h₂]
        exact (continuous_apply _).inv
      · simp only [sel, dif_neg h₁, dif_neg h₂]
        exact continuous_const
  refine ⟨fun V => f fun b => sel b V, ⟨?_, C, fun V => hC _⟩, ?_⟩
  · let _ : MeasurableSpace (InfiniteLattice.LinkVariables (B : Set D.Link)) :=
      borel (InfiniteLattice.LinkVariables (B : Set D.Link))
    have : BorelSpace (InfiniteLattice.LinkVariables (B : Set D.Link)) := ⟨rfl⟩
    exact hf.comp (measurable_pi_iff.2 fun b => (hsel b).measurable)
  · funext U
    simp only [InfiniteLattice.LatticeSymmetry.actOn, Function.comp_apply,
      InfiniteLattice.observableOfLinks]
    congr 1
    funext b
    have hmem : tb b.1 ∈ B ∨ (tb b.1).opposite ∈ B := by
      refine mem_cornerCubeLinks_or_opposite_mem D c _ ?_ ?_
      · exact hv _ b.2.1
      · exact hv _ b.2.2
    change U (tb b.1) = sel b (InfiniteLattice.restrictField U (B : Set D.Link))
    by_cases h₁ : tb b.1 ∈ B
    · simp only [sel, dif_pos h₁]
      rfl
    · have h₂ := hmem.resolve_left h₁
      simp only [sel, dif_neg h₁, dif_pos h₂]
      change U (tb b.1) = (U (tb b.1).opposite)⁻¹
      rw [U.2]
      simp
theorem isBoundedMeasurableInLinks_sum {D : GridSetup} {B : Finset D.Link} {T : Type*} [Fintype T]
    {F : T → D.GaugeField → ℂ} (h : ∀ t, D.IsBoundedMeasurableInLinks B (F t)) :
    D.IsBoundedMeasurableInLinks B fun U => ∑ t, F t U := by
  classical
  choose Φ hΦ hF using h
  refine ⟨∑ t, Φ t, Submodule.sum_mem _ fun t _ => hΦ t, ?_⟩
  funext U
  simp only [InfiniteLattice.observableOfLinks, Finset.sum_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hF t]
  rfl
theorem latticeSymmetry_ext {a : ℝ} {s s' : InfiniteLattice.LatticeSymmetry a}
    (h : s.toFun = s'.toFun) : s = s' := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem finprod_eq_fintype_prod_of_injective {ι T M : Type*} [CommMonoid M] [Fintype T] {e : T → ι}
    (he : Function.Injective e) (φ : ι → M) (h : ∀ i, i ∉ range e → φ i = 1) :
    ∏ᶠ i, φ i = ∏ t, φ (e t) := by
  have h1 : ∏ᶠ i ∈ range e, φ i = ∏ᶠ t, φ (e t) := finprod_mem_range he
  have h2 : ∏ᶠ t, φ (e t) = ∏ t, φ (e t) := finprod_eq_prod_of_fintype _
  rw [← h2, ← h1, finprod_mem_def, Set.mulIndicator_eq_self.2]
  intro i hi
  by_contra hc
  exact hi (h i hc)
theorem statement_holds (hWeight : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hBox : CubeVersusTorus.Statement)
    (hChess : chessboardEstimate_allSides)
    (hFacts : ReflectionGridProperties) : Statement := by
  classical
  intro D
  refine ⟨fun ν hν => exists_isPeriod D hν, ?_⟩
  intro ν p hG hp g hg S hS h hh hside
  obtain ⟨k₀, rfl⟩ := hS
  have hsideT : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m := hside
  obtain ⟨-, -, -, hGrp, -, -, hTor, -, -⟩ := hFacts D g hg
  obtain ⟨hCells, -, -, -, -, hRead, -⟩ := hTor hsideT
  obtain ⟨hChess1, hChess2, -⟩ := hChess D g hg hsideT
  obtain ⟨-, hGrpUniq, -, -, hGrpTrans⟩ := hGrp
  have hL1 : 1 < D.L := by
    have := D.isAdmissible.2
    omega
  obtain ⟨-, -, -, -, -, -, -, hprobW, hnullW, -⟩ :=
    hWeight D.L D.m D.K D.β hL1 D.m.pos D.K.pos
  have hprobν : IsProbabilityMeasure ν := hG.1
  have hp1 : 1 ≤ p := hp.2.1
  have ha : 0 < D.mesh := D.mesh_pos
  have hl : 0 < g.cellSide := zpow_pos (by linarith [D.one_lt_factor]) _
  have hℓ : 0 < D.side := by linarith
  obtain ⟨⟨n, -, hn⟩, -, hCellEq, -, -⟩ := hCells
  have hnl : (n : ℝ) * g.cellSide = D.side := by
    rw [← hn]
    change PeriodicLattice.torusSide D.L D.m / g.cellSide * g.cellSide = PeriodicLattice.torusSide D.L D.m
    field_simp
  have hnposR : (0 : ℝ) < n := by
    by_contra hc
    have : (n : ℝ) * g.cellSide ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) hl.le
    linarith
  have hnpos : 0 < n := by exact_mod_cast hnposR
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = (N : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg hnpos.le).symm⟩
  have hN1 : 1 ≤ N := by exact_mod_cast hnpos
  obtain ⟨M, hMle, hMge⟩ : ∃ M : ℕ, (2 * p) * M ≤ N + 2 * p - 1 ∧ N ≤ (2 * p) * M := by
    refine ⟨(N + 2 * p - 1) / (2 * p), Nat.mul_div_le _ _, ?_⟩
    have h1 := Nat.div_add_mod (N + 2 * p - 1) (2 * p)
    have h2 := Nat.mod_lt (N + 2 * p - 1) (by omega : 0 < 2 * p)
    omega
  have hM1 : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · subst h0
      omega
    · exact h0
  let T : Type := Fin 4 → Fin M
  let w : T → Fin 4 → ℤ := fun t μ => (p : ℤ) * ((t μ : ℕ) : ℤ)
  have hw0 : ∀ t μ, 0 ≤ w t μ := fun t μ => by positivity
  have hwN : ∀ t μ, 2 * w t μ + 1 ≤ (N : ℤ) := fun t μ => by
    have h1 : (t μ : ℕ) + 1 ≤ M := (t μ).2
    have h2 : (2 * p) * ((t μ : ℕ) + 1) ≤ (2 * p) * M := Nat.mul_le_mul_left _ h1
    have h3 : 2 * (p * (t μ : ℕ)) + 1 ≤ N := by
      have : (2 * p) * ((t μ : ℕ) + 1) = 2 * (p * (t μ : ℕ)) + 2 * p := by ring
      omega
    simp only [w]
    exact_mod_cast h3
  let vs : T → InfiniteLattice.LatticePoint D.mesh := fun t =>
    ⟨fun μ => 2 * g.cellSide * (w t μ : ℝ), fun μ => 2 * g.cellRatio * w t μ, fun μ => by
      rw [g.cellSide_eq]
      push_cast
      ring⟩
  have hr : ∀ t : T, ∃ r : g.reflectionGroup, (r.1 : AmbientSpace → AmbientSpace) =
      ChessboardTori.translate (fun μ => 2 * g.cellSide * (w t μ : ℝ)) ∧ g.IsEvenElement r :=
    fun t => hGrpTrans (w t)
  choose r hr1 hr2 using hr
  have hIso : ∀ t, g.toLatticeSym (r t) = InfiniteLattice.shift (vs t) := fun t => by
    apply latticeSymmetry_ext
    exact hr1 t
  let kt : T → Fin 4 → ℤ := fun t μ => k₀ μ + 2 * w t μ
  have hImg : ∀ t, (r t).1 '' g.cell k₀ = g.cell (kt t) := fun t => by
    have hv : ∀ y : AmbientSpace, (r t).1 y = fun μ => y μ + 2 * g.cellSide * (w t μ : ℝ) := fun y =>
      congrFun (hr1 t) y
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      intro μ
      have e : ((r t).1 y) μ - (g.origin μ + g.cellSide * (kt t μ : ℝ)) =
          y μ - (g.origin μ + g.cellSide * (k₀ μ : ℝ)) := by
        rw [hv y]
        simp only [kt]
        push_cast
        ring
      rw [e]
      exact hy μ
    · intro hx
      refine ⟨fun μ => x μ - 2 * g.cellSide * (w t μ : ℝ), fun μ => ?_, ?_⟩
      · have e : (x μ - 2 * g.cellSide * (w t μ : ℝ)) - (g.origin μ + g.cellSide * (k₀ μ : ℝ)) =
            x μ - (g.origin μ + g.cellSide * (kt t μ : ℝ)) := by
          simp only [kt]
          push_cast
          ring
        rw [e]
        exact hx μ
      · rw [hv]
        funext μ
        ring
  have hcopy : ∀ (E : D.GaugeField → ℂ) (t : T),
      g.transportTo (g.cell k₀) (g.cell (kt t)) E =
        (InfiniteLattice.shift (vs t)).actOn E := fun E t => by
    have huniq : ∀ r' : g.reflectionGroup, r'.1 '' g.cell k₀ = g.cell (kt t) → r' = r t := fun r' h' =>
      (hGrpUniq k₀ (kt t)).unique h' (hImg t)
    rw [g.transportTo_eq_transport (hImg t) huniq, ReflectionGrid.transport, hIso t]
    have hs : orientationSign (r t).1 = 1 := hr2 t
    rw [hs]
    funext U
    simp [Conventions.signedConjFun, Conventions.signedConj]
  let c : AmbientSpace := fun μ => g.origin μ + g.cellSide * (k₀ μ : ℝ)
  have hc : D.IsDualLatticePoint c := fun μ => by
    obtain ⟨i, hi⟩ := g.origin_mem μ
    refine ⟨i + g.cellRatio * k₀ μ, ?_⟩
    simp only [c]
    rw [hi, g.cellSide_eq]
    push_cast
    ring
  have hinbox : ∀ t, ∀ x ∈ interior (g.cell k₀), x + (vs t : AmbientSpace) ∈ D.cornerCube c :=
    fun t x hx μ => by
      have hx' := (interior_subset hx) μ
      have h1 : (0 : ℝ) ≤ w t μ := by exact_mod_cast hw0 t μ
      have h2 : 2 * (w t μ : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hwN t μ
      have h3 : g.cellSide * (2 * (w t μ : ℝ) + 1) ≤ g.cellSide * (N : ℝ) :=
        mul_le_mul_of_nonneg_left h2 hl.le
      have h4 : (0 : ℝ) ≤ g.cellSide * (w t μ : ℝ) := mul_nonneg hl.le h1
      have h5 : g.cellSide * (N : ℝ) = D.side := by
        rw [mul_comm]
        exact_mod_cast hnl
      have e : (x + (vs t : AmbientSpace)) μ = x μ + 2 * g.cellSide * (w t μ : ℝ) := rfl
      obtain ⟨h6, h7⟩ := hx'
      simp only [c]
      rw [e]
      constructor <;> nlinarith
  let Acast : D.GaugeField → ℂ := fun U => (h U : ℂ)
  have hobs : InfiniteLattice.IsBoundedObservable Acast := isBoundedObservable_of_mem_cellObservables hh
  have hobsT : ∀ t, InfiniteLattice.IsBoundedObservable
      ((InfiniteLattice.shift (vs t)).actOn Acast) := fun t =>
    (isBoundedMeasurableInLinks_shift (vs t) (hinbox t) hh).isBoundedObservable
  let Hs : T → D.GaugeField → ℝ := fun t U =>
    h ((InfiniteLattice.shift (vs t)).pullbackField U)
  let H : D.GaugeField → ℝ := fun U => ∑ t, Hs t U
  obtain ⟨Cb, hCb⟩ := hobs.2
  have hmeasH0 : Measurable h := by
    have : h = fun U => (Acast U).re := by
      funext U
      simp [Acast]
    rw [this]
    exact Complex.measurable_re.comp hobs.1
  have hmeasHs : ∀ t, Measurable (Hs t) := fun t => by
    have : Hs t = fun U => ((InfiniteLattice.shift (vs t)).actOn Acast U).re := by
      funext U
      simp [Hs, Acast, InfiniteLattice.LatticeSymmetry.actOn]
    rw [this]
    exact Complex.measurable_re.comp (hobsT t).1
  have hbd : ∀ U, ‖h U‖ ≤ Cb := fun U => by
    have := hCb U
    simpa [Acast] using this
  have hbdHs : ∀ t U, ‖Hs t U‖ ≤ Cb := fun t U => hbd _
  have hint0 : Integrable h ν :=
    Integrable.of_bound hmeasH0.aestronglyMeasurable Cb (ae_of_all _ hbd)
  have hintHs : ∀ t, Integrable (Hs t) ν := fun t =>
    Integrable.of_bound (hmeasHs t).aestronglyMeasurable Cb (ae_of_all _ (hbdHs t))
  have hsame : ∀ t, ∫ U, Hs t U ∂ν = ∫ U, h U ∂ν := fun t => by
    have hinv : InfiniteLattice.IsSymmetricUnder ν (InfiniteLattice.shift (vs t)) := by
      refine hp.2.2 (vs t) ⟨fun μ => 2 * g.cellRatio * ((t μ : ℕ) : ℤ), fun μ => ?_⟩
      change 2 * g.cellSide * (((p : ℤ) * ((t μ : ℕ) : ℤ) : ℤ) : ℝ) = _
      rw [g.cellSide_eq]
      push_cast
      ring
    have h1 := hinv Acast hobs
    have h2 : ∫ U, (InfiniteLattice.shift (vs t)).actOn Acast U ∂ν =
        ((∫ U, Hs t U ∂ν : ℝ) : ℂ) := integral_ofReal
    have h3 : ∫ U, Acast U ∂ν = ((∫ U, h U ∂ν : ℝ) : ℂ) := integral_ofReal
    rw [h2, h3] at h1
    exact_mod_cast h1
  have hcard : Fintype.card T = M ^ 4 := by
    simp [T]
  have hintH : ∫ U, H U ∂ν = ((M : ℝ) ^ 4) * ∫ U, h U ∂ν := by
    have h1 : ∫ U, H U ∂ν = ∑ t, ∫ U, Hs t U ∂ν :=
      integral_finsetSum _ fun t _ => hintHs t
    rw [h1, Finset.sum_congr rfl fun t _ => hsame t, Finset.sum_const, Finset.card_univ, hcard]
    simp
  have hHb : D.IsBoundedMeasurableInLinks (D.cornerCubeLinks c) fun U => (H U : ℂ) := by
    have h1 := isBoundedMeasurableInLinks_sum (D := D) (B := D.cornerCubeLinks c) (T := T)
      (F := fun t => (InfiniteLattice.shift (vs t)).actOn Acast)
      fun t => isBoundedMeasurableInLinks_shift (vs t) (hinbox t) hh
    have e : (fun U => (H U : ℂ)) = fun U => ∑ t,
        (InfiniteLattice.shift (vs t)).actOn Acast U := by
      funext U
      simp only [H]
      push_cast
      rfl
    rw [e]
    exact h1
  have hboxc := (hBox D c hc).2.2 ν hG H hHb
  let E₀ : D.GaugeField → ℂ := fun U => (Real.exp (h U) : ℂ)
  have hE₀ : E₀ ∈ ReflectionGrid.cellObservables (D := D) (g.cell k₀) := exp_mem_cellObservables hh
  let C₀ : Set D.Torus := D.proj '' g.cell k₀
  let Ct : T → Set D.Torus := fun t => D.proj '' g.cell (kt t)
  let F₀ : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ := D.liftedObservable E₀
  have hC₀ : C₀ ∈ g.torusCellSet := ⟨_, ⟨k₀, rfl⟩, rfl⟩
  have hCt : ∀ t, Ct t ∈ g.torusCellSet := fun t => ⟨_, ⟨kt t, rfl⟩, rfl⟩
  have hread := hRead (g.cell k₀) ⟨k₀, rfl⟩ E₀ hE₀
  have hF₀ : F₀ ∈ g.torusCellObservables C₀ := hread.1
  let e : T → g.torusCellSet := fun t => ⟨Ct t, hCt t⟩
  have he : Function.Injective e := by
    intro t t' hee
    have hCC : Ct t = Ct t' := congrArg Subtype.val hee
    obtain ⟨j, hj⟩ := (hCellEq (kt t) (kt t')).1 hCC
    funext μ
    apply Fin.ext
    have h1 : kt t μ - kt t' μ = (N : ℤ) * j μ := by
      have := hj μ
      rw [hn] at this
      exact_mod_cast this
    have h2 : (N : ℤ) ∣ 2 * (w t μ - w t' μ) := ⟨j μ, by
      rw [← h1]
      simp only [kt]
      ring⟩
    have h3 : |2 * (w t μ - w t' μ)| < (N : ℤ) := by
      rw [abs_lt]
      constructor <;> linarith [hwN t μ, hwN t' μ, hw0 t μ, hw0 t' μ]
    have h4 := Int.eq_zero_of_abs_lt_dvd h2 h3
    have h5 : w t μ = w t' μ := by omega
    have hp0 : (p : ℤ) ≠ 0 := by
      have : (1 : ℤ) ≤ p := by exact_mod_cast hp1
      omega
    have h6 := mul_left_cancel₀ hp0 h5
    exact_mod_cast h6
  let Fc : g.torusCellSet → (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ := fun C =>
    if C ∈ range e then g.torusTransportTo C₀ C.1 F₀ else fun _ => 1
  have hcop : ∀ C ∈ g.torusCellSet, g.torusTransportTo C₀ C F₀ ∈ g.torusCellObservables C ∧
      g.cellChessboardSeminorm C (g.torusTransportTo C₀ C F₀) = g.cellChessboardSeminorm C₀ F₀ :=
    fun C hC => ((hChess2 C₀ hC₀).1 F₀ hF₀).2.2.2.2.2.1 C hC
  have hFc : ∀ C, Fc C ∈ g.torusCellObservables C.1 := fun C => by
    by_cases hC : C ∈ range e
    · simp only [Fc, if_pos hC]
      exact (hcop C.1 C.2).1
    · simp only [Fc, if_neg hC]
      exact (hChess2 C.1 C.2).2.1
  have hchess := hChess1.1 Fc hFc
  have hprodR : ∏ᶠ C, g.cellChessboardSeminorm C.1 (Fc C) =
      g.cellChessboardSeminorm C₀ F₀ ^ (M ^ 4) := by
    rw [finprod_eq_fintype_prod_of_injective he (fun C => g.cellChessboardSeminorm C.1 (Fc C)) fun C hC => by
      simp only [Fc, if_neg hC]
      exact (hChess2 C.1 C.2).2.2]
    have h1 : ∀ t, g.cellChessboardSeminorm (e t).1 (Fc (e t)) = g.cellChessboardSeminorm C₀ F₀ :=
      fun t => by
        simp only [Fc, if_pos (mem_range_self t)]
        exact (hcop (e t).1 (e t).2).2
    rw [Finset.prod_congr rfl fun t _ => h1 t, Finset.prod_const, Finset.card_univ, hcard]
  have hU : ∀ U ∈ D.torusFields,
      (∏ᶠ C, Fc C U) = ((Real.exp (H (D.liftField U)) : ℝ) : ℂ) := fun U hU' => by
    rw [finprod_eq_fintype_prod_of_injective he (fun C => Fc C U) fun C hC => by
      simp only [Fc, if_neg hC]]
    have h1 : ∀ t, Fc (e t) U = ((Real.exp (Hs t (D.liftField U)) : ℝ) : ℂ) := fun t => by
      simp only [Fc, if_pos (mem_range_self t)]
      have h2 := hread.2.2 (g.cell (kt t)) ⟨kt t, rfl⟩ hU'
      rw [hcopy] at h2
      exact h2.symm
    rw [Finset.prod_congr rfl fun t _ => h1 t]
    simp only [H]
    rw [Real.exp_sum]
    push_cast
    rfl
  obtain ⟨Er, hErdef⟩ : ∃ x : ℝ, x =
      D.expect ((fun U => Real.exp (H U)) ∘ D.liftField) := ⟨_, rfl⟩
  rw [← hErdef] at hboxc
  have haeW : ∀ᵐ U ∂(PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β), U ∈ D.torusFields :=
    ae_iff.2 hnullW
  have hEq : D.periodicExpectation (fun U => ∏ᶠ C, Fc C U) = (Er : ℂ) := by
    have h1 : D.periodicExpectation (fun U => ∏ᶠ C, Fc C U) =
        ∫ U, ((Real.exp (H (D.liftField U)) : ℝ) : ℂ)
          ∂(PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β) :=
      integral_congr_ae (haeW.mono fun U hU' => hU U hU')
    rw [h1, hErdef]
    exact integral_ofReal
  have hmeasH : Measurable H := Finset.measurable_fun_sum _ fun t _ => hmeasHs t
  let B : ℝ := ∑ _t : T, Cb
  have hbdH : ∀ U, |H U| ≤ B := fun U => by
    have := norm_sum_le_of_le (f := fun t => Hs t U) Finset.univ (fun t _ => hbdHs t U)
    simpa [H, B] using this
  have hmeasE : Measurable ((fun U => Real.exp (H U)) ∘ D.liftField) :=
    (Real.measurable_exp.comp hmeasH).comp (InfiniteLattice.measurable_liftField _ _ _)
  have hintE : Integrable ((fun U => Real.exp (H U)) ∘ D.liftField)
      (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β) := by
    refine Integrable.of_bound hmeasE.aestronglyMeasurable (Real.exp B) (ae_of_all _ fun U => ?_)
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (hbdH _))
  have hElow : Real.exp (-B) ≤ Er := by
    have h1 := integral_mono (integrable_const (Real.exp (-B))) hintE fun U =>
      Real.exp_le_exp.2 (neg_le_of_abs_le (hbdH (D.liftField U)))
    rw [hErdef]
    simp only [integral_const, probReal_univ, one_smul] at h1
    exact h1
  have hErpos : 0 < Er := lt_of_lt_of_le (Real.exp_pos _) hElow
  have hch0 : 0 ≤ g.cellChessboardSeminorm C₀ F₀ := Real.rpow_nonneg (norm_nonneg _) _
  obtain ⟨ch, hchdef⟩ : ∃ x : ℝ, x = g.cellChessboardSeminorm C₀ F₀ := ⟨_, rfl⟩
  rw [← hchdef] at hch0 hprodR
  have hEle : Er ≤ ch ^ (M ^ 4) := by
    have h1 := hchess
    rw [hEq, hprodR, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hErpos] at h1
    exact h1
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM1
  have hchpos : 0 < ch := by
    rcases hch0.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      rw [← h', zero_pow (by positivity)] at hEle
      linarith
  have hlog : Real.log Er ≤ (M : ℝ) ^ 4 * Real.log ch := by
    have h1 := Real.log_le_log hErpos hEle
    rw [Real.log_pow] at h1
    push_cast at h1
    exact h1
  change ∫ U, h U ∂ν ≤ Real.log (g.cellChessboardSeminorm C₀ F₀) +
    cubeComparisonConstant * (2 * (p : ℝ)) ^ 4 * D.β * (g.cellSide / D.mesh) ^ 3 * (g.cellSide / D.side)
  rw [← hchdef]
  have hJ : (0 : ℝ) < (M : ℝ) ^ 4 := by positivity
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNM : (N : ℝ) ≤ 2 * (p : ℝ) * M := by exact_mod_cast hMge
  have hN4 : (N : ℝ) ^ 4 ≤ (2 * (p : ℝ)) ^ 4 * (M : ℝ) ^ 4 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hNR.le hNM 4
  have hsideN : D.side = (N : ℝ) * g.cellSide := by
    rw [← hnl]
    norm_cast
  have hA : 0 ≤ cubeComparisonConstant * D.β * (g.cellSide / D.mesh) ^ 3 := by
    have hb : (0 : ℝ) ≤ cubeComparisonConstant := by norm_num [cubeComparisonConstant]
    have hβ := D.beta_pos
    positivity
  have key : cubeComparisonConstant * D.β * (D.side / D.mesh) ^ 3 ≤ (M : ℝ) ^ 4 *
      (cubeComparisonConstant * (2 * (p : ℝ)) ^ 4 * D.β * (g.cellSide / D.mesh) ^ 3 *
        (g.cellSide / D.side)) := by
    have e1 : (D.side / D.mesh) ^ 3 = (N : ℝ) ^ 3 * (g.cellSide / D.mesh) ^ 3 := by
      rw [hsideN, mul_div_assoc, mul_pow]
    have e2 : g.cellSide / D.side = 1 / (N : ℝ) := by
      rw [hsideN]
      field_simp
    have h3 : (N : ℝ) ^ 3 ≤ (2 * (p : ℝ)) ^ 4 * (M : ℝ) ^ 4 / N := by
      rw [le_div_iff₀ hNR]
      calc (N : ℝ) ^ 3 * N = (N : ℝ) ^ 4 := by ring
        _ ≤ _ := hN4
    rw [e1, e2]
    calc cubeComparisonConstant * D.β * ((N : ℝ) ^ 3 * (g.cellSide / D.mesh) ^ 3)
        = cubeComparisonConstant * D.β * (g.cellSide / D.mesh) ^ 3 * (N : ℝ) ^ 3 := by ring
      _ ≤ cubeComparisonConstant * D.β * (g.cellSide / D.mesh) ^ 3 *
          ((2 * (p : ℝ)) ^ 4 * (M : ℝ) ^ 4 / N) :=
        mul_le_mul_of_nonneg_left h3 hA
      _ = _ := by ring
  have hfin : (M : ℝ) ^ 4 * ∫ U, h U ∂ν ≤ (M : ℝ) ^ 4 * (Real.log ch +
      cubeComparisonConstant * (2 * (p : ℝ)) ^ 4 * D.β * (g.cellSide / D.mesh) ^ 3 *
        (g.cellSide / D.side)) := by
    rw [hintH] at hboxc
    rw [mul_add]
    linarith
  exact le_of_mul_le_mul_left hfin hJ
end MirrorGridsAllSides.JensenBoundFromPeriods
end
end YangMills.Construction
