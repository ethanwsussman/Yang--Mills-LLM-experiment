import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import YangMills.Construction.OneLoopLaw.PlaneWavesUnderMotionsOfTheLatticeProof
import YangMills.Construction.PeriodicOperators.SchurTestOnWeightedFunctions
import YangMills.Construction.Towers.CountsOfCrossingsOnASide
import YangMills.Construction.Towers.CrossingAverageOnASide
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.CrossingSmoothingContraction
theorem pauliCoeff_of_mem_traceless {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a X = OneLoop.pauliCoordinateEquiv ⟨X, hX⟩ a :=
  dif_pos hX
theorem pauliFamily_mem_traceless (a : Fin 3) :
    Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem pauliCoeff_pauliFamily (a' a : Fin 3) :
    pauliCoeff a' (Matrices.ComplexMatrix2.pauliFamily a) = if a' = a then 1 else 0 := by
  rw [pauliCoeff_of_mem_traceless (pauliFamily_mem_traceless a)]
  obtain ⟨h0, h1, h2⟩ := Matrices.ComplexMatrix2.pauliFamily_apply
  fin_cases a <;> fin_cases a'
  all_goals
    simp [OneLoop.pauliCoordinateEquiv, Matrices.ComplexMatrix2.pauliFamily, OneLoop.pauliX,
      OneLoop.pauliY, OneLoop.pauliZ]
  all_goals (try field_simp)
  all_goals (try norm_num)
theorem pauliCoeff_smul_pauliFamily (z : ℂ) (a' a : Fin 3) :
    pauliCoeff a' (z • Matrices.ComplexMatrix2.pauliFamily a) = if a' = a then z else 0 := by
  have hz : z • Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.traceless :=
    (Matrices.ComplexMatrix2.traceless).smul_mem z (pauliFamily_mem_traceless a)
  rw [pauliCoeff_of_mem_traceless hz]
  have e : (⟨z • Matrices.ComplexMatrix2.pauliFamily a, hz⟩ : Matrices.ComplexMatrix2.traceless) =
      z • ⟨Matrices.ComplexMatrix2.pauliFamily a, pauliFamily_mem_traceless a⟩ := rfl
  rw [e, map_smul, Pi.smul_apply, ← pauliCoeff_of_mem_traceless (pauliFamily_mem_traceless a),
    pauliCoeff_pauliFamily]
  split_ifs <;> simp
theorem list_sum_map_eq_ite_of_nodup {α : Type} (g : α → Matrices.ComplexMatrix2) (b : α)
    (X : Matrices.ComplexMatrix2) (Γ : List α)
    (hnd : Γ.Nodup) (hg : open Classical in ∀ β ∈ Γ, g β = if β = b then X else 0) :
    open Classical in (Γ.map g).sum = if b ∈ Γ then X else 0 := by
  classical
  induction Γ with
  | nil => simp
  | cons h t ih =>
    obtain ⟨hh, ht⟩ := List.nodup_cons.mp hnd
    rw [List.map_cons, List.sum_cons, hg h List.mem_cons_self,
      ih ht fun β hβ => hg β (List.mem_cons_of_mem _ hβ)]
    by_cases e : h = b
    · subst e
      simp [hh]
    · have e' : b ≠ h := fun q => e q.symm
      simp [e, e']
theorem piSingle_one_self {ι : Type} (d : DecidableEq ι) (j : ι) :
    @Pi.single ι (fun _ => ℂ) _ d j 1 j = 1 :=
  Pi.single_eq_same _ _
theorem piSingle_one_of_ne {ι : Type} (d : DecidableEq ι) {j j' : ι} (h : j' ≠ j) :
    @Pi.single ι (fun _ => ℂ) _ d j 1 j' = 0 :=
  Pi.single_eq_of_ne h _
variable {L n k i : ℕ}
theorem ofCoeffs_piSingle_of_positive (a : Fin 3) (b : PositiveEdge L n k i) (β : Edge L n k i)
    (hβ : β.IsPositivelyOriented) :
    open Classical in
    (edgePauliCoordinates L n k i).ofCoeffs (Pi.single (a, b) 1) β =
      if β = b.1 then Matrices.ComplexMatrix2.pauliFamily a else 0 := by
  classical
  have key : ∀ f : Fin 3 × PositiveEdge L n k i → ℂ, f (a, b) = 1 → (∀ q, q ≠ (a, b) → f q = 0) →
      ofPauliCoeffs f ⟨β, hβ⟩ = if β = b.1 then Matrices.ComplexMatrix2.pauliFamily a else 0 := by
    intro f hf hf'
    unfold ofPauliCoeffs
    by_cases e : β = b.1
    · subst e
      rw [if_pos rfl, Finset.sum_eq_single a]
      · rw [show ((a, (⟨b.1, hβ⟩ : PositiveEdge L n k i))) = (a, b) from rfl, hf, one_smul]
      · intro a' _ h
        have : ((a', (⟨b.1, hβ⟩ : PositiveEdge L n k i))) ≠ (a, b) := fun q =>
          h (congrArg Prod.fst q)
        rw [hf' _ this, zero_smul]
      · simp
    · rw [if_neg e]
      refine Finset.sum_eq_zero fun a' _ => ?_
      have : ((a', (⟨β, hβ⟩ : PositiveEdge L n k i))) ≠ (a, b) := fun q =>
        e (congrArg Subtype.val (congrArg Prod.snd q))
      rw [hf' _ this, zero_smul]
  dsimp only [edgePauliCoordinates]
  unfold extendOddly
  rw [if_pos hβ]
  beta_reduce
  rw [dif_pos hβ]
  exact key _ (piSingle_one_self _ _) fun q h => piSingle_one_of_ne _ h
theorem crossingKernel_apply (hform : ∀ (c : PositiveEdge L n k (i + 1)) (x : Vertex L n k i),
      (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock 1 c.1.source →
        (PeriodicLattice.crossingPath c.1 x).Nodup ∧
          ∀ b ∈ PeriodicLattice.crossingPath c.1 x, b.IsPositivelyOriented)
    [Finite (Vertex L n k i)] (a' a : Fin 3) (c : PositiveEdge L n k (i + 1))
    (b : PositiveEdge L n k i) :
    crossingKernel L n k i (a', c) (a, b) =
      if a' = a then
        ((((L : ℝ)⁻¹ * (L : ℝ) ^ (-4 : ℤ) *
          ((crossingSites L n k i (i + 1) c.1 b.1).ncard : ℝ) : ℝ)) : ℂ)
      else 0 := by
  classical
  set E : Edge L n k i → Matrices.ComplexMatrix2 :=
    (edgePauliCoordinates L n k i).ofCoeffs (Pi.single (a, b) 1) with hE
  have hT : (crossingSites L n k i (i + 1) c.1 b.1).Finite := Set.toFinite _
  have hsum : ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) c.1.source,
      edgeFormPathSum E (PeriodicLattice.crossingPath c.1 x) =
      (((crossingSites L n k i (i + 1) c.1 b.1).ncard : ℂ)) •
        Matrices.ComplexMatrix2.pauliFamily a := by
    have h1 : i + 1 - i = 1 := by omega
    have hstep : ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) c.1.source,
        edgeFormPathSum E (PeriodicLattice.crossingPath c.1 x) =
          if b.1 ∈ PeriodicLattice.crossingPath c.1 x then
            Matrices.ComplexMatrix2.pauliFamily a else 0 := by
      intro x hx
      obtain ⟨hnd, hpos⟩ := hform c x hx
      exact list_sum_map_eq_ite_of_nodup E b.1 (Matrices.ComplexMatrix2.pauliFamily a) _ hnd
        fun β hβ => ofCoeffs_piSingle_of_positive a b β (hpos β hβ)
    rw [finsum_mem_congr rfl hstep]
    have hind : ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) c.1.source,
        (if b.1 ∈ PeriodicLattice.crossingPath c.1 x then
          Matrices.ComplexMatrix2.pauliFamily a else 0) =
        ∑ᶠ x ∈ crossingSites L n k i (i + 1) c.1 b.1, Matrices.ComplexMatrix2.pauliFamily a := by
      rw [finsum_mem_def, finsum_mem_def]
      congr 1
      funext x
      by_cases hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) c.1.source
      · by_cases hb : b.1 ∈ PeriodicLattice.crossingPath c.1 x
        · have : x ∈ crossingSites L n k i (i + 1) c.1 b.1 :=
            ⟨by rw [h1]; exact hx, hb⟩
          rw [Set.indicator_of_mem hx, Set.indicator_of_mem this, if_pos hb]
        · have : x ∉ crossingSites L n k i (i + 1) c.1 b.1 := fun q => hb q.2
          rw [Set.indicator_of_mem hx, Set.indicator_of_notMem this, if_neg hb]
      · have : x ∉ crossingSites L n k i (i + 1) c.1 b.1 := fun q =>
          hx (by have := q.1; rw [h1] at this; exact this)
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem this]
    rw [hind, finsum_mem_eq_finite_toFinset_sum _ hT, Finset.sum_const,
      Set.ncard_eq_toFinset_card _ hT, Nat.cast_smul_eq_nsmul]
  have hval : crossingKernel L n k i (a', c) (a, b) =
      pauliCoeff a' (((L : ℝ)⁻¹ • crossingSmoothing L n k i E) c.1) := rfl
  have hreal : ∀ (r : ℝ) (Y : Matrices.ComplexMatrix2), r • Y = (r : ℂ) • Y := fun r Y => by
    ext p q
    simp [Matrix.smul_apply]
  rw [hval, Pi.smul_apply]
  unfold crossingSmoothing
  rw [hsum, hreal, smul_smul, smul_smul, pauliCoeff_smul_pauliFamily]
  by_cases e : a' = a
  · rw [if_pos e, if_pos e]
    simp only [PeriodicLattice.inverseFourthPowerWeight]
    push_cast
    ring
  · rw [if_neg e, if_neg e]
theorem normAtMostOne_of_counts_of_schur (hCounts : CrossingCountsOnTorus)
    (hSchur : PeriodicOperators.SchurTest.Holds) : normAtMostOne := by
  classical
  intro L hL n k i hn hik
  have hL0 : 0 < L := by have := hL.2; omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
  have hLne : (L : ℝ) ≠ 0 := hLr.ne'
  have : Finite (Vertex L n k i) := SeparatedSequences.BaseParameters.site_finite hL0 n _
  have : Finite (Vertex L n k (i + 1)) := SeparatedSequences.BaseParameters.site_finite hL0 n _
  have : Finite (Edge L n k i) :=
    Finite.of_injective (fun b : Edge L n k i => (b.source, b.target)) fun _ _ h =>
      PeriodicLattice.Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have : Finite (Edge L n k (i + 1)) :=
    Finite.of_injective (fun b : Edge L n k (i + 1) => (b.source, b.target)) fun _ _ h =>
      PeriodicLattice.Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  let _ : Fintype (PositiveEdge L n k i) := Fintype.ofFinite _
  let _ : Fintype (PositiveEdge L n k (i + 1)) := Fintype.ofFinite _
  obtain ⟨hrow, hcol, hform⟩ := hCounts L hL n k i (i + 1) hn (by omega) (by omega) hik
  have h1 : i + 1 - i = 1 := by omega
  rw [h1] at hrow hcol
  have hform' : ∀ (c : PositiveEdge L n k (i + 1)) (x : Vertex L n k i),
      (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock 1 c.1.source →
        (PeriodicLattice.crossingPath c.1 x).Nodup ∧
          ∀ b ∈ PeriodicLattice.crossingPath c.1 x, b.IsPositivelyOriented := by
    intro c x hx
    exact hform c x (by rw [h1]; exact hx)
  set K : ℝ := (L : ℝ)⁻¹ * (L : ℝ) ^ (-4 : ℤ) with hK
  let N : PositiveEdge L n k (i + 1) → PositiveEdge L n k i → ℝ := fun c b =>
    K * ((crossingSites L n k i (i + 1) c.1 b.1).ncard : ℝ)
  have hN : ∀ c b, 0 ≤ N c b := fun c b => by positivity
  have hKrow : K * (L : ℝ) ^ (5 * 1) = 1 := by
    rw [hK, zpow_neg]
    have : (L : ℝ) ^ (4 : ℤ) = (L : ℝ) ^ 4 := by norm_cast
    rw [this]
    field_simp
  have hKcol : K * (L : ℝ) ^ 1 = (L : ℝ) ^ (-4 : ℤ) := by
    rw [hK]
    field_simp
  have hrows : ∀ c, Summable (N c) ∧ ∑' b, N c b ≤ 1 := by
    intro c
    refine ⟨(hasSum_fintype _).summable, ?_⟩
    have h := hrow c
    rw [finsum_eq_sum_of_fintype] at h
    rw [tsum_fintype, ← Finset.mul_sum, h, hKrow]
  have hcols : ∀ b, Summable (fun c => N c b) ∧ ∑' c, N c b ≤ (L : ℝ) ^ (-4 : ℤ) := by
    intro b
    refine ⟨(hasSum_fintype _).summable, ?_⟩
    have h := hcol b
    rw [finsum_eq_sum_of_fintype] at h
    rw [tsum_fintype, ← Finset.mul_sum, h, hKcol]
  have hoff : ∀ (b b' : Fin 3) (y : PositiveEdge L n k (i + 1)) (x : PositiveEdge L n k i),
      b' ≠ b → crossingKernel L n k i (b', y) (b, x) = 0 := by
    intro b b' y x h
    rw [crossingKernel_apply hform', if_neg h]
  have hdiag : ∀ (b : Fin 3) (y : PositiveEdge L n k (i + 1)) (x : PositiveEdge L n k i),
      ‖crossingKernel L n k i (b, y) (b, x)‖ ≤ N y x := by
    intro b y x
    rw [crossingKernel_apply hform', if_pos rfl, Complex.norm_real, Real.norm_of_nonneg (hN y x)]
  have hspace : meshAt L k (i + 1) ^ 4 * (L : ℝ) ^ (-4 : ℤ) = meshAt L k i ^ 4 := by
    have e : meshAt L k (i + 1) = (L : ℝ) * meshAt L k i := by
      unfold meshAt
      rw [show ((i + 1 : ℕ) : ℤ) - (k : ℤ) = 1 + ((i : ℤ) - (k : ℤ)) by push_cast; ring,
        zpow_add₀ hLne, zpow_one]
    rw [e, zpow_neg, mul_pow]
    have : (L : ℝ) ^ (4 : ℤ) = (L : ℝ) ^ 4 := by norm_cast
    rw [this]
    field_simp
  have hpos : 0 < meshAt L k i := by unfold meshAt; positivity
  have hpos' : 0 < meshAt L k (i + 1) := by unfold meshAt; positivity
  have hmain := hSchur.2 (PositiveEdge L n k i) (PositiveEdge L n k (i + 1))
    (crossingKernel L n k i) N
    (meshWeight (meshAt L k i)) (meshWeight (meshAt L k (i + 1)))
    (meshAt L k i ^ 4) (meshAt L k (i + 1) ^ 4) 1 ((L : ℝ) ^ (-4 : ℤ)) 1
    (by positivity) (by positivity) zero_le_one (fun _ => rfl) (fun _ => rfl) hoff hdiag hrows hcols
    (by rw [one_mul, hspace]; simp)
  exact hmain.2 Set.univ
end YangMills.Construction.Tower.CrossingSmoothingContraction
end
