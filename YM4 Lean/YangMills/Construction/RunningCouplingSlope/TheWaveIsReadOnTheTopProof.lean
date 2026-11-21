import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometriesProof
import YangMills.Construction.RunningCouplingSlope.TheWaveIsReadOnTheTop
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open scoped Quaternion Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
variable {L n k : ℕ}
private theorem halfPeriod_levelDepth :
    PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k k) = L ^ n := by
  simp [PeriodicLattice.halfPeriod, PeriodicLattice.levelDepth]
private theorem offsetSite_eq_iff
    (hC : PeriodicLattice.SublatticeCoordinates L n (PeriodicLattice.levelDepth k k))
    (a b : Fin 4 → ℤ) :
    (PeriodicLattice.offsetSite (0 : Vertex L n k k) a = PeriodicLattice.offsetSite 0 b) ↔
      ∀ μ, a μ ≡ b μ [ZMOD ((2 * L ^ n : ℕ) : ℤ)] := by
  have h := hC.2.2.2.2.1 0 a b
  rwa [halfPeriod_levelDepth] at h
private theorem offsetSite_single (μ : Fin 4) :
    PeriodicLattice.offsetSite (0 : Vertex L n k k) (Pi.single μ 1) =
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ := by
  simp [PeriodicLattice.offsetSite, Pi.single_apply]
private theorem offsetSite_zero :
    PeriodicLattice.offsetSite (0 : Vertex L n k k) 0 = 0 := by
  simp [PeriodicLattice.offsetSite]
private theorem offsetSite_add (a b : Fin 4 → ℤ) :
    PeriodicLattice.offsetSite (0 : Vertex L n k k) (a + b) =
      PeriodicLattice.offsetSite 0 a + PeriodicLattice.offsetSite 0 b := by
  simp [PeriodicLattice.offsetSite, add_smul, Finset.sum_add_distrib]
private theorem not_modEq_zero_of_small {M : ℕ} (hM : 2 < M) {t : ℤ} (h0 : 0 < t) (h2 : t ≤ 2) :
    ¬ t ≡ 0 [ZMOD (M : ℤ)] := by
  intro h
  have h' : (M : ℤ) ∣ t := Int.modEq_zero_iff_dvd.mp h
  have := Int.le_of_dvd h0 h'
  omega
private theorem two_lt_period (hL : 13 ≤ L) (hn : 0 < n) : 2 < 2 * L ^ n := by
  have : 1 < L ^ n := Nat.one_lt_pow hn.ne' (by omega)
  omega
private theorem unitStep_injective
    (hC : PeriodicLattice.SublatticeCoordinates L n (PeriodicLattice.levelDepth k k))
    (hL : 13 ≤ L) (hn : 0 < n) {μ ν : Fin 4}
    (h : PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ =
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) ν) :
    μ = ν := by
  by_contra hne
  rw [← offsetSite_single (k := k), ← offsetSite_single (k := k)] at h
  have h1 := (offsetSite_eq_iff hC _ _).1 h μ
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h1
  exact not_modEq_zero_of_small (two_lt_period hL hn) (by norm_num) (by norm_num) h1
private theorem not_opposite_positive
    (hC : PeriodicLattice.SublatticeCoordinates L n (PeriodicLattice.levelDepth k k))
    (hL : 13 ≤ L) (hn : 0 < n) (b : Edge L n k k) (hb : b.IsPositivelyOriented) :
    ¬ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, hμ⟩ := hb
  rintro ⟨ν, hν⟩
  have hν' : b.source - b.target = PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) ν := hν
  have hs : PeriodicLattice.offsetSite (0 : Vertex L n k k) (Pi.single μ 1 + Pi.single ν 1) =
      PeriodicLattice.offsetSite 0 0 := by
    rw [offsetSite_add, offsetSite_single, offsetSite_single, offsetSite_zero, ← hμ, ← hν']
    abel
  have h1 := (offsetSite_eq_iff hC _ _).1 hs μ
  simp only [Pi.add_apply, Pi.zero_apply, Pi.single_eq_same] at h1
  by_cases e : ν = μ
  · subst e
    simp only [Pi.single_eq_same] at h1
    exact not_modEq_zero_of_small (two_lt_period hL hn) (by norm_num) (by norm_num) h1
  · simp only [Pi.single_eq_of_ne (Ne.symm e)] at h1
    exact not_modEq_zero_of_small (two_lt_period hL hn) (by norm_num) (by norm_num) h1
private theorem inv_mem_of_mem {u : Matrices.ComplexMatrix2}
    (hu : u ∈ PeriodicLattice.compactGaugeGroup) : u⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
private theorem inv_inv_of_mem {u : Matrices.ComplexMatrix2}
    (hu : u ∈ PeriodicLattice.compactGaugeGroup) : (u⁻¹)⁻¹ = u := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
private theorem matExp_I_smul_mem {A : Matrices.ComplexMatrix2}
    (hA : A ∈ Matrices.ComplexMatrix2.hermitianTraceless) :
    Matrices.ComplexMatrix2.matExp (Complex.I • A) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.matExp_mem_compactGaugeGroup <;> assumption
private theorem expTwist_mem_fieldSpace
    (hC : PeriodicLattice.SublatticeCoordinates L n (PeriodicLattice.levelDepth k k))
    (hL : 13 ≤ L) (hn : 0 < n) (B : edgeFormSpace L n k k) (u : ℝ) :
    PeriodicLattice.expTwist (u • (B : Edge L n k k → Matrices.ComplexMatrix2)) (fun _ => 1) ∈
      fieldSpace L n k k := by
  have hpos : ∀ b : Edge L n k k, b.IsPositivelyOriented →
      Matrices.ComplexMatrix2.matExp
          (Complex.I • ((u • (B : Edge L n k k → Matrices.ComplexMatrix2)) b)) * 1 ∈
        PeriodicLattice.compactGaugeGroup := by
    intro b hb
    rw [mul_one]
    exact matExp_I_smul_mem (Matrices.ComplexMatrix2.hermitianTraceless.smul_mem u (B.2.1 b hb))
  have positive_or_opposite : ∀ b : Edge L n k k,
      b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by
    intro b
    obtain ⟨μ, h | h⟩ := b.isNeighbour
    · exact Or.inl ⟨μ, h⟩
    · refine Or.inr ⟨μ, ?_⟩
      change b.source - b.target = _
      rw [← neg_sub, h, neg_neg]
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · simp only [PeriodicLattice.expTwist, if_pos hb]
      exact hpos b hb
    · simp only [PeriodicLattice.expTwist, if_neg hb]
      exact inv_mem_of_mem (hpos _ ((positive_or_opposite b).resolve_left hb))
  · by_cases hb : b.IsPositivelyOriented
    · have hb' := not_opposite_positive hC hL hn b hb
      have hrr : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
      simp only [PeriodicLattice.expTwist, if_pos hb, if_neg hb', hrr]
    · have hb' : b.opposite.IsPositivelyOriented := (positive_or_opposite b).resolve_left hb
      simp only [PeriodicLattice.expTwist, if_pos hb', if_neg hb]
      rw [inv_inv_of_mem (hpos _ hb')]
private theorem quaternionToMatrix_thirdGenerator (c : ℝ) :
    SoftAverages.quaternionToMatrix
        ((c • thirdGenerator : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) =
      Complex.I • (c • Matrices.ComplexMatrix2.pauliFamily 2) := by
  have e : ((c • thirdGenerator : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) = ⟨0, c, 0, 0⟩ := by
    apply Quaternion.ext
    · show c • (0 : ℝ) = 0
      simp
    · show c • (1 : ℝ) = c
      simp
    · show c • (0 : ℝ) = 0
      simp
    · show c • (0 : ℝ) = 0
      simp
  rw [e]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SoftAverages.quaternionToMatrix, Matrices.ComplexMatrix2.pauliFamily, OneLoop.pauliZ]
private theorem matExp_thirdGenerator (c : ℝ) :
    Matrices.ComplexMatrix2.matExp (Complex.I • (c • Matrices.ComplexMatrix2.pauliFamily 2)) =
      SoftAverages.quaternionToMatrix
        (NormedSpace.exp ((c • thirdGenerator : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])) := by
  have h := NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (𝔸 := ℍ[ℝ]) (𝔹 := Matrices.ComplexMatrix2)
    SoftAverages.quaternionToMatrixRingHom SoftAverages.continuous_quaternionToMatrix
    ((c • thirdGenerator : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])
    (by rw [NormedSpace.expSeries_radius_eq_top]; simp)
  change SoftAverages.quaternionToMatrix _ =
    NormedSpace.exp (SoftAverages.quaternionToMatrix _) at h
  rw [h, quaternionToMatrix_thirdGenerator]
private theorem forwardFrom_eq_iff
    (hC : PeriodicLattice.SublatticeCoordinates L n (PeriodicLattice.levelDepth k k))
    (hL : 13 ≤ L) (hn : 0 < n) (y z : TorusFields.TorusSite (2 * L ^ n)) (μ : Fin 4) :
    (PeriodicLattice.Bond.forwardFrom (topVertexOf (L := L) (n := n) (k := k) z) μ =
        PeriodicLattice.Bond.forwardFrom (PeriodicLattice.offsetSite 0 (centredCoords y))
          SlopeCoefficient.secondAxis) ↔ y = z ∧ μ = SlopeCoefficient.secondAxis := by
  constructor
  · intro h
    have ht : topVertexOf (L := L) (n := n) (k := k) z =
        PeriodicLattice.offsetSite 0 (centredCoords y) :=
      congrArg PeriodicLattice.Bond.source h
    have hh := congrArg PeriodicLattice.Bond.target h
    refine ⟨?_, ?_⟩
    · funext ν
      have h1 := (offsetSite_eq_iff hC _ _).1 ht ν
      have h2 := (ZMod.intCast_eq_intCast_iff _ _ _).2 h1
      simpa [centredCoords] using h2.symm
    · change topVertexOf z + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ =
        PeriodicLattice.offsetSite 0 (centredCoords y) +
          PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k)
            SlopeCoefficient.secondAxis at hh
      rw [ht] at hh
      exact unitStep_injective hC hL hn (add_left_cancel hh)
  · rintro ⟨rfl, rfl⟩
    have e : topVertexOf (L := L) (n := n) (k := k) y =
        PeriodicLattice.offsetSite 0 (centredCoords y) := by
      refine (offsetSite_eq_iff hC _ _).2 fun ν => ?_
      refine (ZMod.intCast_eq_intCast_iff _ _ _).1 ?_
      simp [centredCoords]
    rw [e]
private theorem planeWaveValues_forwardFrom [NeZero (2 * L ^ n)]
    (hC : PeriodicLattice.SublatticeCoordinates L n (PeriodicLattice.levelDepth k k))
    (hL : 13 ≤ L) (hn : 0 < n) (f : TorusFields.TorusSite (2 * L ^ n) → ℝ)
    (z : TorusFields.TorusSite (2 * L ^ n)) (μ : Fin 4) :
    planeWaveValues L n k f (PeriodicLattice.Bond.forwardFrom (topVertexOf z) μ) =
      if μ = SlopeCoefficient.secondAxis then f z • Matrices.ComplexMatrix2.pauliFamily 2 else 0 := by
  classical
  have hpos : (PeriodicLattice.Bond.forwardFrom
      (topVertexOf (L := L) (n := n) (k := k) z) μ).IsPositivelyOriented :=
    ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
  have each : ∀ y : TorusFields.TorusSite (2 * L ^ n),
      pauliUnitForm L n k (centredCoords y) (PeriodicLattice.Bond.forwardFrom (topVertexOf z) μ) =
        if y = z ∧ μ = SlopeCoefficient.secondAxis then Matrices.ComplexMatrix2.pauliFamily 2
        else 0 := by
    intro y
    simp only [pauliUnitForm, extendOddly, if_pos hpos]
    by_cases h : y = z ∧ μ = SlopeCoefficient.secondAxis
    · rw [if_pos h, if_pos ((forwardFrom_eq_iff hC hL hn y z μ).2 h)]
    · rw [if_neg h, if_neg (fun e => h ((forwardFrom_eq_iff hC hL hn y z μ).1 e))]
  simp only [planeWaveValues, Finset.sum_apply, Pi.smul_apply, each]
  by_cases hμ : μ = SlopeCoefficient.secondAxis
  · simp [hμ]
  · simp [hμ]
theorem planeWaveRepresentsTorusField_holds (hC : PeriodicLattice.CoordinateDescription) :
    PlaneWaveRepresentsTorusField := by
  intro L _ hL k n hk hn f B hB u
  have hCo : PeriodicLattice.SublatticeCoordinates L n (PeriodicLattice.levelDepth k k) :=
    (hC L n hL.1 hL.2 hn).1 _ (by simp [PeriodicLattice.levelDepth])
  refine ⟨expTwist_mem_fieldSpace hCo hL.2 hn B u, fun z μ => ?_⟩
  have hpos : (PeriodicLattice.Bond.forwardFrom
      (topVertexOf (L := L) (n := n) (k := k) z) μ).IsPositivelyOriented :=
    ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
  have hw := planeWaveValues_forwardFrom hCo hL.2 hn f z μ
  rw [← hB] at hw
  simp only [PeriodicLattice.expTwist, if_pos hpos, mul_one, Pi.smul_apply, hw]
  simp only [SlopeCoefficient.expAlong, planeWaveOnTorus]
  by_cases hμ : μ = SlopeCoefficient.secondAxis
  · simp only [if_pos hμ, smul_smul]
    exact matExp_thirdGenerator (u * f z)
  · simp only [if_neg hμ, smul_zero]
    have h0 := matExp_thirdGenerator 0
    simp only [zero_smul, smul_zero] at h0
    exact h0
end YangMills.Construction.RunningCouplingSlope
end
