import YangMills.Construction.InfiniteLattice.StatesReflectionPositiveAtEveryLatticeMirror
import YangMills.Construction.ReflectionPositivity.FivePointInequalityPassesToTheLimit
import YangMills.Construction.ReflectionPositivity.LatticeFormulaForTheScalarProduct
import Mathlib
set_option autoImplicit false
open Filter Topology MeasureTheory
open scoped ComplexOrder NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.FivePointLimit
open ReflectionPositivity.AxisMirror (MirrorData)
open ReflectionPositivity.TupleForm (PositiveSpan reflectedCorrelation)
open InfiniteLattice (LatticePoint AmbientSpace refinedSpacing latticeSubgroup axisStep)
open LimitConventions (ApproxTriple)
open ReflectionPositivity.LatticeScalarProduct (latticeExpectation conjReflMulShift meshAt)
open LatticeConventions (timeAxis)
open ReflectionPositivity.Reconstruction (fivePointCombination spatialBasisVec embedSpatial timeBasisVec)
open PeriodicLattice (adicGridPoints)
open SeparatedTuples (FormalSpan)
theorem intCast_mul_mem_adicGridPoints {L : ℕ} {s : ℝ} (hs : s ∈ adicGridPoints L) (m : ℤ) :
    (m : ℝ) * s ∈ adicGridPoints L := by
  obtain ⟨k, n, rfl⟩ := (PeriodicLattice.mem_adicGridPoints_iff L s).1 hs
  exact (PeriodicLattice.mem_adicGridPoints_iff L _).2 ⟨k, m * n, by push_cast; ring⟩
theorem exists_int_pi_single (ν μ : Fin 4) :
    ∃ m : ℤ, (Pi.single ν (1 : ℝ) : AmbientSpace) μ = m := by
  by_cases h : μ = ν
  · exact ⟨1, by simp [h]⟩
  · exact ⟨0, by simp [Pi.single_eq_of_ne h]⟩
theorem embedSpatial_spatialBasisVec (i : Fin 3) :
    embedSpatial (spatialBasisVec i) = (Pi.single i.castSucc (1 : ℝ) : AmbientSpace) := by
  fin_cases i <;> ext μ <;> fin_cases μ <;> simp [embedSpatial, spatialBasisVec]
theorem timeBasisVec_eq : timeBasisVec = (Pi.single timeAxis (1 : ℝ) : AmbientSpace) := rfl
theorem coe_nsmul_axisStep (a : ℝ) (k : ℕ) (μ : Fin 4) :
    ((k • axisStep a μ : LatticePoint a) : AmbientSpace) =
      ((k : ℝ) * a) • (Pi.single μ (1 : ℝ) : AmbientSpace) := by
  ext ν
  by_cases h : ν = μ
  · subst h
    simp [axisStep]
  · simp [axisStep, Pi.single_eq_of_ne h]
theorem latticeExpectation_eq_reflectedCorrelation (D : MirrorData) (T : ApproxTriple D.L)
    (Z : FormalSpan) (j : ℕ+)
    (v : LatticePoint ((meshAt D T j : LatticeConventions.Spacing) : ℝ)) (w : AmbientSpace)
    (hw : (v : AmbientSpace) = w) :
    latticeExpectation D T Z Z w j =
      LatticeConventions.SiteFrame.reflectedCorrelation (meshAt D T j) timeAxis (T.state j)
        (T.spanRep j Z) v := by
  subst hw
  unfold latticeExpectation LatticeConventions.SiteFrame.reflectedCorrelation
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  unfold conjReflMulShift
  rw [dif_pos v.2]
  rfl
theorem tendsto_refinedSpacing (D : MirrorData) (T : ApproxTriple D.L) :
    Tendsto (fun j => refinedSpacing D.L (T.cutoff j)) atTop (𝓝 0) := by
  have hL : (1 : ℝ) < D.L := by
    have h := D.isAdmissible.2
    exact_mod_cast (by omega : 1 < D.L)
  have hinv : (D.L : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hL
  have hnat : Tendsto (fun j => ((T.cutoff j : ℕ+) : ℕ)) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [tendsto_atTop.1 T.tendsto_cutoff b.succPNat] with j hj
    have : (b.succPNat : ℕ) ≤ (T.cutoff j : ℕ) := hj
    simp only [Nat.succPNat_coe] at this
    omega
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 (by linarith)) hinv).comp hnat
  refine h.congr fun j => ?_
  simp [refinedSpacing, PeriodicLattice.meshSize, zpow_neg, inv_pow]
theorem fivePointInequalityInLimit_of_latticeFormula
    (hFormula : ReflectionPositivity.LatticeScalarProduct.LatticeFormula)
    (hOne : LatticeConventions.ReflectionPositiveStates.Statement) :
    FivePointInequalityInLimit := by
  intro D T σ _ hRP hLim i t ht Z
  have hB : ReflectionPositivity.ApproximatingSequences.LatticeApproximation.IsBoundedForSomeM D T := ‹_›
  obtain ⟨⟨δ, hδ, hZ, -⟩, hall⟩ := hFormula D T σ hRP hB hLim Z Z
  obtain ⟨hrep, hadic, -⟩ := hall δ hδ hZ hZ
  have htA : (t : ℝ) ∈ adicGridPoints D.L := ht.1
  have htpos : (0 : ℝ) < t := ht.2
  have hadicInt : ∀ v : AmbientSpace, (∀ μ, ∃ m : ℤ, v μ = m * t) →
      ∀ μ, v μ ∈ adicGridPoints D.L := by
    intro v hv μ
    obtain ⟨m, hm⟩ := hv μ
    rw [hm]
    exact intCast_mul_mem_adicGridPoints htA m
  have hsv : embedSpatial (spatialBasisVec i) = (Pi.single i.castSucc (1 : ℝ) : AmbientSpace) :=
    embedSpatial_spatialBasisVec i
  have hsv3 : embedSpatial (spatialBasisVec i) TimeAxis.timeIdx = 0 := rfl
  have hte : timeBasisVec TimeAxis.timeIdx = 1 := by
    simp [timeBasisVec_eq, TimeAxis.timeIdx, timeAxis]
  have hunitT : ∀ μ, ∃ m : ℤ, timeBasisVec μ = m := exists_int_pi_single timeAxis
  have hunitS : ∀ μ, ∃ m : ℤ, embedSpatial (spatialBasisVec i) μ = m := by
    rw [hsv]
    exact exists_int_pi_single _
  have a0 : ∀ μ, (0 : AmbientSpace) μ ∈ adicGridPoints D.L := hadicInt _ fun μ => ⟨0, by simp⟩
  have a1 : ∀ μ, (((t : ℝ) • timeBasisVec : AmbientSpace)) μ ∈ adicGridPoints D.L :=
    hadicInt _ fun μ => by
      obtain ⟨m, hm⟩ := hunitT μ
      exact ⟨m, by simp [hm, mul_comm]⟩
  have a2 : ∀ μ, (((2 * t : ℝ) • timeBasisVec : AmbientSpace)) μ ∈ adicGridPoints D.L :=
    hadicInt _ fun μ => by
      obtain ⟨m, hm⟩ := hunitT μ
      exact ⟨2 * m, by simp [hm]; ring⟩
  have a3 : ∀ μ, (((t : ℝ) • timeBasisVec + (t : ℝ) • embedSpatial (spatialBasisVec i) :
      AmbientSpace)) μ ∈ adicGridPoints D.L := hadicInt _ fun μ => by
    obtain ⟨m, hm⟩ := hunitT μ
    obtain ⟨m', hm'⟩ := hunitS μ
    exact ⟨m + m', by simp [hm, hm']; ring⟩
  have a4 : ∀ μ, (((t : ℝ) • timeBasisVec - (t : ℝ) • embedSpatial (spatialBasisVec i) :
      AmbientSpace)) μ ∈ adicGridPoints D.L := hadicInt _ fun μ => by
    obtain ⟨m, hm⟩ := hunitT μ
    obtain ⟨m', hm'⟩ := hunitS μ
    exact ⟨m - m', by simp [hm, hm']; ring⟩
  have p0 : 0 ≤ TimeAxis.timeComponent (0 : AmbientSpace) := by simp [TimeAxis.timeComponent]
  have p1 : 0 ≤ TimeAxis.timeComponent ((t : ℝ) • timeBasisVec : AmbientSpace) := by
    simp only [TimeAxis.timeComponent, Pi.smul_apply, smul_eq_mul, hte]
    linarith
  have p2 : 0 ≤ TimeAxis.timeComponent ((2 * t : ℝ) • timeBasisVec : AmbientSpace) := by
    simp only [TimeAxis.timeComponent, Pi.smul_apply, smul_eq_mul, hte]
    linarith
  have p3 : 0 ≤ TimeAxis.timeComponent ((t : ℝ) • timeBasisVec +
      (t : ℝ) • embedSpatial (spatialBasisVec i) : AmbientSpace) := by
    simp only [TimeAxis.timeComponent, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hte, hsv3]
    linarith
  have p4 : 0 ≤ TimeAxis.timeComponent ((t : ℝ) • timeBasisVec -
      (t : ℝ) • embedSpatial (spatialBasisVec i) : AmbientSpace) := by
    simp only [TimeAxis.timeComponent, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hte, hsv3]
    linarith
  have hlim : Tendsto (fun j =>
      latticeExpectation D T Z.1 Z.1 0 j - 4 * latticeExpectation D T Z.1 Z.1 ((t : ℝ) • timeBasisVec) j +
        latticeExpectation D T Z.1 Z.1 ((2 * t : ℝ) • timeBasisVec) j +
        latticeExpectation D T Z.1 Z.1
          ((t : ℝ) • timeBasisVec + (t : ℝ) • embedSpatial (spatialBasisVec i)) j +
        latticeExpectation D T Z.1 Z.1
          ((t : ℝ) • timeBasisVec - (t : ℝ) • embedSpatial (spatialBasisVec i)) j)
      atTop (𝓝 (fivePointCombination σ Z t i)) :=
    ((((hadic 0 a0 p0).2.1.sub ((hadic _ a1 p1).2.1.const_mul 4)).add (hadic _ a2 p2).2.1).add
      (hadic _ a3 p3).2.1).add (hadic _ a4 p4).2.1
  refine ge_of_tendsto hlim ?_
  filter_upwards [(tendsto_refinedSpacing D T).eventually (Iio_mem_nhds hδ), (hadic _ a1 p1).1]
    with j hj hint
  have hapos : 0 < refinedSpacing D.L (T.cutoff j) := (meshAt D T j).2
  obtain ⟨n, hn⟩ := hint TimeAxis.timeIdx
  have htn : (t : ℝ) = (n : ℝ) * refinedSpacing D.L (T.cutoff j) := by
    have h1 : ((t : ℝ) • timeBasisVec : AmbientSpace) TimeAxis.timeIdx = t := by
      simp only [Pi.smul_apply, smul_eq_mul, hte, mul_one]
    rw [h1] at hn
    field_simp at hn
    rw [hn, mul_comm]
  have hnpos : 0 < n := by
    have hprod : (0 : ℝ) < (n : ℝ) * refinedSpacing D.L (T.cutoff j) := htn ▸ htpos
    have hreal : (0 : ℝ) < n := (pos_iff_pos_of_mul_pos hprod).2 hapos
    exact_mod_cast hreal
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hnpos.le
  have hk : 1 ≤ k := by omega
  have htk : (t : ℝ) = (k : ℝ) * refinedSpacing D.L (T.cutoff j) := by
    simpa using htn
  have hF := (hrep j hj.le).1
  have hfive := (hOne (meshAt D T j) (T.state j) (hRP j).1 (hRP j).2).2.2.2 i
    ⟨T.spanRep j Z.1, hF⟩ k hk
  unfold LatticeConventions.SiteFrame.FivePointBound at hfive
  have hstep : ((k • axisStep ((meshAt D T j : LatticeConventions.Spacing) : ℝ) timeAxis :
      LatticePoint _) : AmbientSpace) = (t : ℝ) • timeBasisVec := by
    rw [coe_nsmul_axisStep, timeBasisVec_eq, ← htk]
  have hstep2 : (((2 * k) • axisStep ((meshAt D T j : LatticeConventions.Spacing) : ℝ) timeAxis :
      LatticePoint _) : AmbientSpace) = (2 * t : ℝ) • timeBasisVec := by
    rw [coe_nsmul_axisStep, timeBasisVec_eq, htk]
    congr 1
    push_cast
    ring
  have hstepS : ((k • axisStep ((meshAt D T j : LatticeConventions.Spacing) : ℝ)
      (LatticeConventions.SpatialDirection.toDirection i) : LatticePoint _) : AmbientSpace) =
      (t : ℝ) • embedSpatial (spatialBasisVec i) := by
    rw [coe_nsmul_axisStep, hsv, ← htk]
    rfl
  rw [latticeExpectation_eq_reflectedCorrelation D T Z.1 j 0 0 rfl,
    latticeExpectation_eq_reflectedCorrelation D T Z.1 j _ _ hstep,
    latticeExpectation_eq_reflectedCorrelation D T Z.1 j _ _ hstep2,
    latticeExpectation_eq_reflectedCorrelation D T Z.1 j
      (k • axisStep _ timeAxis + k • axisStep _ (LatticeConventions.SpatialDirection.toDirection i)) _
      (by rw [AddSubgroup.coe_add, hstep, hstepS]),
    latticeExpectation_eq_reflectedCorrelation D T Z.1 j
      (k • axisStep _ timeAxis - k • axisStep _ (LatticeConventions.SpatialDirection.toDirection i)) _
      (by rw [AddSubgroup.coe_sub, hstep, hstepS])]
  exact hfive
end YangMills.Construction.ReflectionPositivity.FivePointLimit
