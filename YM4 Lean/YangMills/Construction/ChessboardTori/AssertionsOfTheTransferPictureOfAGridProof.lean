import YangMills.Construction.ChessboardTori.AssertionsOfTheTransferPictureOfAGrid
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
namespace TransferSetup
variable {D : ChessboardSetup} (T : TransferSetup D)
theorem sliceTime_injective : Function.Injective T.sliceTime := by
  intro i j hij
  have hne := D.mesh_pos.ne'
  simp only [sliceTime] at hij
  have hij' : (i : ℝ) * D.mesh = (j : ℝ) * D.mesh := by linarith
  exact_mod_cast mul_right_cancel₀ hne hij'
theorem sliceTimesAndWalls (m : SlabCount) (hts : T.SliceTimesAndSlabs m) :
    T.SliceTimesAndWalls := by
  obtain ⟨hrange, -, -, hwall, -⟩ := hts
  refine ⟨fun x hx => ?_, fun i => ?_, fun k => ⟨(hwall k).1, fun x hx => ?_⟩⟩
  · have hx' : x ∈ range T.sliceTime := by
      rw [hrange]
      exact hx
    obtain ⟨i, rfl⟩ := hx'
    exact ⟨i, rfl, fun j hj => T.sliceTime_injective hj⟩
  · have hi : T.sliceTime i ∈ range T.sliceTime := mem_range_self i
    rw [hrange] at hi
    exact hi
  · obtain ⟨n, hn⟩ := hx
    obtain ⟨c, hc⟩ := T.grid.origin_mem T.axis
    have hmesh := D.mesh_pos
    have hside : T.grid.cellSide = ((T.ratioNat : ℤ) : ℝ) * D.mesh := by
      rw [T.natCast_ratioNat]
      exact T.grid.cellSide_eq
    have htime : ∀ z : ℤ, T.sliceTime z = ((c + z : ℤ) : ℝ) * D.mesh := by
      intro z
      simp only [sliceTime, hc]
      push_cast
      ring
    have hlow : T.grid.origin T.axis + (k : ℝ) * T.grid.cellSide =
        ((2 * (c + k * (T.ratioNat : ℤ)) + 1 : ℤ) : ℝ) * (D.mesh / 2) := by
      rw [hc, hside]
      push_cast
      ring
    have hhigh : T.grid.origin T.axis + ((k : ℝ) + 1) * T.grid.cellSide =
        ((2 * (c + k * (T.ratioNat : ℤ) + (T.ratioNat : ℤ)) + 1 : ℤ) : ℝ) * (D.mesh / 2) := by
      rw [hc, hside]
      push_cast
      ring
    have hxhalf : x T.axis = ((2 * n T.axis : ℤ) : ℝ) * (D.mesh / 2) := by
      rw [hn]
      push_cast
      ring
    have hcmp : ∀ u v : ℤ, (u : ℝ) * (D.mesh / 2) < (v : ℝ) * (D.mesh / 2) ↔ u < v := by
      intro u v
      constructor
      · intro huv
        exact_mod_cast lt_of_mul_lt_mul_right huv (half_pos hmesh).le
      · intro huv
        exact mul_lt_mul_of_pos_right (by exact_mod_cast huv) (half_pos hmesh)
    have hxt : ∀ s : ℤ, x T.axis = T.sliceTime (k * (T.ratioNat : ℤ) + s) ↔
        n T.axis = c + (k * (T.ratioNat : ℤ) + s) := by
      intro s
      rw [htime, hn]
      constructor
      · intro heq
        exact_mod_cast mul_right_cancel₀ hmesh.ne' heq
      · intro heq
        rw [heq]
    rw [hlow, hhigh, hxhalf, hcmp, hcmp, ← hxhalf]
    simp only [hxt]
    constructor
    · rintro ⟨hlo, hhi⟩
      exact ⟨n T.axis - c - k * (T.ratioNat : ℤ), by omega, by omega, by omega⟩
    · rintro ⟨s, hs₁, hs₂, hs₃⟩
      constructor <;> omega
theorem slabEdgesAndFields (m : SlabCount) (hedges : T.EdgesAndFields m)
    (hslabs : T.SlabDecompositionProperties m) : T.SlabEdgesAndFields m := by
  obtain ⟨e₁, e₂, -, -⟩ := hedges
  obtain ⟨s₁, s₂, -⟩ := hslabs
  refine ⟨e₁, e₂, s₁, s₂, fun k η => ?_⟩
  obtain ⟨U, hU⟩ := s₁.bijective.2 (fun _ => η, fun _ => 1)
  exact ⟨U, congrFun (congrArg Prod.fst hU) k⟩
theorem facesAndEnergies (m : SlabCount) (hfaces : T.FacesOfSlices m) :
    T.FacesAndEnergies m := by
  obtain ⟨hbij, htrans, haxial⟩ := hfaces
  exact ⟨hbij, fun U => ⟨fun i q => (htrans i q).1 U, fun i b => (haxial i b).2 U⟩⟩
theorem facePartition (m : SlabCount) (hcross : T.CrossingFaces m)
    (hin : T.FacesInSlab m) : T.FacePartition m := by
  obtain ⟨c₁, c₂, -⟩ := hcross
  exact ⟨fun p => (c₁ p).symm, c₂, fun k p => (hin k).1 p⟩
theorem slabSliceIndex_zero_injective (m : SlabCount) {k k' : ZMod (m : ℕ)}
    (hkk : T.slabSliceIndex m k 0 = T.slabSliceIndex m k' 0) : k = k' := by
  have hratio : (T.ratioNat : ℤ) ≠ 0 := by
    have := T.two_le_ratioNat
    omega
  obtain ⟨z, hz⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hkk
  have hdvd : ((m : ℕ) : ℤ) ∣ (k'.cast : ℤ) - (k.cast : ℤ) := by
    refine ⟨z, mul_right_cancel₀ hratio ?_⟩
    push_cast at hz
    linear_combination hz
  have hcast := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr hdvd
  simpa using hcast
def IsUnitIntervalReal (z : ℂ) : Prop := ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ z = t
theorem IsUnitIntervalReal.mul {z w : ℂ} (hz : IsUnitIntervalReal z)
    (hw : IsUnitIntervalReal w) : IsUnitIntervalReal (z * w) := by
  obtain ⟨t, ht₀, ht₁, rfl⟩ := hz
  obtain ⟨s, hs₀, hs₁, rfl⟩ := hw
  exact ⟨t * s, mul_pos ht₀ hs₀, mul_le_one₀ ht₁ hs₀.le hs₁, by push_cast; rfl⟩
theorem IsUnitIntervalReal.prod {ι : Type} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, IsUnitIntervalReal (f i)) : IsUnitIntervalReal (∏ i ∈ s, f i) :=
  Finset.prod_induction f IsUnitIntervalReal (fun _ _ => IsUnitIntervalReal.mul)
    ⟨1, one_pos, le_rfl, by simp⟩ hf
theorem isUnitIntervalReal_exp (D : ChessboardSetup) {x : ℝ} (hx : 0 ≤ x) :
    IsUnitIntervalReal (Complex.exp (-(D.β : ℂ) * (x : ℂ))) := by
  refine ⟨Real.exp (-D.β * x), Real.exp_pos _, Real.exp_le_one_iff.mpr ?_, ?_⟩
  · have := mul_nonneg D.beta_pos.le hx
    linarith
  · rw [Complex.ofReal_exp]
    push_cast
    rfl
theorem faceAction_nonneg (htr : GaugeGroupTraceFacts) (q : T.TransverseFace)
    (ξ : T.EdgeField) : 0 ≤ T.faceAction q ξ := by
  have hre := (htr (T.faceHolonomy ξ q)).2.1
  have hnorm := Complex.re_le_norm
    (Matrices.ComplexMatrix2.fullTrace (T.faceHolonomy ξ q : Matrices.ComplexMatrix2))
  simp only [faceAction]
  linarith
theorem isUnitIntervalReal_boltzmannFactor (D : ChessboardSetup) (htr : GaugeGroupTraceFacts)
    (u : Conventions.StandingParameters.gaugeGroup) :
    IsUnitIntervalReal (boltzmannFactor D u) := by
  obtain ⟨him, hnorm, -⟩ := htr u
  have hreal : Matrices.ComplexMatrix2.fullTrace (u : Matrices.ComplexMatrix2) =
      (((Matrices.ComplexMatrix2.fullTrace (u : Matrices.ComplexMatrix2)).re : ℝ) : ℂ) :=
    Complex.ext rfl (by simp [him])
  have hle := Complex.re_le_norm (Matrices.ComplexMatrix2.fullTrace (u : Matrices.ComplexMatrix2))
  have hfactor : boltzmannFactor D u =
      Complex.exp (-(D.β : ℂ) *
        (((1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (u : Matrices.ComplexMatrix2)).re : ℝ)) : ℂ)) := by
    rw [boltzmannFactor]
    congr 2
    push_cast
    rw [← hreal]
  rw [hfactor]
  exact isUnitIntervalReal_exp D (by linarith)
theorem isUnitIntervalReal_wilsonSlabBoltzmann (htr : GaugeGroupTraceFacts) (η : T.SlabConfig) :
    IsUnitIntervalReal (T.wilsonSlabBoltzmann η) := by
  refine IsUnitIntervalReal.mul ?_ ?_
  · exact IsUnitIntervalReal.prod _ _ fun j _ => IsUnitIntervalReal.prod _ _ fun q _ =>
      isUnitIntervalReal_exp D (T.faceAction_nonneg htr q _)
  · exact IsUnitIntervalReal.prod _ _ fun j _ => IsUnitIntervalReal.prod _ _ fun b _ =>
      isUnitIntervalReal_boltzmannFactor D htr _
theorem slabBoltzmannBounds (m : SlabCount) (htr : GaugeGroupTraceFacts)
    (hW : T.SlabBoltzmannWeights m) : T.SlabBoltzmannBounds := by
  refine ⟨?_, fun η => ?_⟩
  · have hcont := ((hW (fun _ => 0) ⟨0, by simp⟩).1 0).1
    rwa [T.slabBoltzmann_zero m 0] at hcont
  · obtain ⟨t, ht₀, ht₁, heq⟩ := T.isUnitIntervalReal_wilsonSlabBoltzmann htr η
    rw [heq]
    exact ⟨Complex.ofReal_im t, by simpa using ht₀, by simpa using ht₁⟩
theorem boltzmannFactorization (m : SlabCount) (hc : T.CrossingFaces m)
    (hb : Function.Bijective (T.faceOfSlices m)) (hV : T.SlabDecompositionProperties m)
    (hW : T.SlabBoltzmannWeights m) : T.BoltzmannFactorization m := by
  classical
  intro U
  have hin : ∀ k : ZMod (m : ℕ),
      (∏ᶠ (p : (T.torusPeriods m).Face) (_ : T.IsInSlab m k p),
        Complex.exp (-(D.β : ℂ) * ((T.torusPeriods m).faceEnergy U p : ℂ))) =
      T.wilsonSlabBoltzmann (T.slabRestriction m k U) := fun k => by
    have hk := ((hW (fun _ => 0) ⟨0, by simp⟩).1 k).2.2 U
    rw [T.slabBoltzmann_zero m k] at hk
    simpa only [zero_sub] using hk.symm
  refine ⟨fun k b => hV.2.2 U k b, hin, ?_⟩
  have hfin : Finite (T.torusPeriods m).Face := Finite.of_surjective _ hb.2
  let _ := Fintype.ofFinite (T.torusPeriods m).Face
  set g : (T.torusPeriods m).Face → ℂ := fun p =>
    Complex.exp (-(D.β : ℂ) * ((T.torusPeriods m).faceEnergy U p : ℂ)) with hg
  have hA : Complex.exp (-(D.β : ℂ) * ((T.torusPeriods m).wilsonAction U : ℂ)) = ∏ p, g p := by
    have hsum : (T.torusPeriods m).wilsonAction U = ∑ p, (T.torusPeriods m).faceEnergy U p :=
      finsum_eq_sum_of_fintype _
    rw [hsum]
    push_cast
    rw [Finset.mul_sum, Complex.exp_sum]
  let f : (T.torusPeriods m).Face → Option (ZMod (m : ℕ)) := fun p =>
    if hp : ∃ k, T.IsInSlab m k p then some hp.choose else none
  have hsome : ∀ p k, f p = some k ↔ T.IsInSlab m k p := by
    intro p k
    constructor
    · intro hfp
      by_cases hp : ∃ k, T.IsInSlab m k p
      · have hch : hp.choose = k := by simpa [f, hp] using hfp
        exact hch ▸ hp.choose_spec
      · simp [f, hp] at hfp
    · intro hpk
      have hp : ∃ k, T.IsInSlab m k p := ⟨k, hpk⟩
      have hu : hp.choose = k := by
        rcases hc.1 p with hu | hcr
        · exact hu.unique hp.choose_spec hpk
        · exact absurd hpk (hcr k)
      simp [f, hp, hu]
  have hnone : ∀ p, f p = none ↔ T.IsCrossingFace m p := by
    intro p
    constructor
    · intro hfp k hk
      rw [(hsome p k).mpr hk] at hfp
      exact absurd hfp (by simp)
    · intro hcp
      have hp : ¬ ∃ k, T.IsInSlab m k p := fun ⟨k, hk⟩ => hcp k hk
      simp [f, hp]
  have hslab : ∀ k, ∏ p with f p = some k, g p =
      T.wilsonSlabBoltzmann (T.slabRestriction m k U) := by
    intro k
    rw [← hin k]
    symm
    exact finprod_cond_eq_prod_of_cond_iff _ fun {p} _ => by simp [hsome]
  let φ : ZMod (m : ℕ) × T.PositiveTransverseEdge → (T.torusPeriods m).Face :=
    fun x => T.axialFace m (T.slabSliceIndex m x.1 0) x.2
  have hφ : Function.Injective φ := by
    rintro ⟨k, b⟩ ⟨k', b'⟩ hkb
    have hsum : (Sum.inr (T.slabSliceIndex m k 0, b) :
        (T.SliceLabel m × T.TransverseFace) ⊕ (T.SliceLabel m × T.PositiveTransverseEdge)) =
        Sum.inr (T.slabSliceIndex m k' 0, b') := hb.1 hkb
    have hpair := Prod.mk.inj (Sum.inr.inj hsum)
    rw [T.slabSliceIndex_zero_injective m hpair.1, hpair.2]
  have hcross : ∏ p with f p = none, g p = ∏ k : ZMod (m : ℕ), ∏ b : T.PositiveTransverseEdge,
      boltzmannFactor D (T.axialHolonomy (T.sliceField m U (T.slabSliceIndex m k 0))
        (T.sliceField m U (T.slabSliceIndex m k 1))
        (T.axialField m U (T.slabSliceIndex m k 0)) b) := by
    have hset : (Finset.univ.filter fun p => f p = none) = Finset.univ.image φ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hnone,
        hc.2.1 p, Prod.exists]
      constructor
      · rintro ⟨k, b, rfl⟩
        exact ⟨k, b, rfl⟩
      · rintro ⟨k, b, rfl⟩
        exact ⟨k, b, rfl⟩
    rw [hset, Finset.prod_image hφ.injOn, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun b _ => ?_
    exact (hV.2.2 U k b).symm
  rw [hA, ← Finset.prod_fiberwise Finset.univ f g, Fintype.prod_option, hcross,
    Finset.prod_mul_distrib, mul_comm]
  exact congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => hslab k) rfl
end TransferSetup
theorem GridTransferAssertions.holds (hsetup : TransferAssertions.Statement) :
    GridTransferAssertions.Statement := fun D T _ m => by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ := hsetup D T m
  exact ⟨T.sliceTimesAndWalls m h₁, T.slabEdgesAndFields m h₂ h₇,
    T.facesAndEnergies m h₄, T.facePartition m h₅ h₈, h₆,
    T.boltzmannFactorization m h₅ h₄.1 h₇ h₉,
    T.slabBoltzmannBounds m h₃ h₉⟩
end YangMills.Construction.ChessboardTori
end
