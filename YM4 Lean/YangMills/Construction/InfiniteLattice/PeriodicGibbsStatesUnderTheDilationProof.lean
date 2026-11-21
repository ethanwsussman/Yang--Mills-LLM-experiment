import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnObservablesProof
import YangMills.Construction.InfiniteLattice.AdmissiblePositionsOfAMirror
import YangMills.Construction.InfiniteLattice.DataOfADiagonalPictureProof
import YangMills.Construction.InfiniteLattice.EquivalentFormsOfTheGibbsProperty
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAndPlaquettesAtEverySpacingProof
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesUnderTheDilation
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open MeasureTheory Set InfiniteLattice
open LatticeConventions (NormalHyperplane IsAxialNormal IsFaceDiagonalNormal Point euclidDot
  euclidNorm basisVector)
open GibbsAtFixedSpacing.ScalingToUnitSpacing (TransportsGibbsMeasures)
noncomputable section
namespace GibbsAtFixedSpacing.PeriodicGibbsUnderRescaling
variable {a β : ℝ}
private def probOfMeasure (ν : Measure (GaugeField a)) (h : IsProbabilityMeasure ν) : BorelProb a :=
  (⟨ν, h⟩ : GaugeFieldProbability a)
private theorem pushToUnit_linearCombination (c d : ENNReal) (ν₁ ν₂ : Measure (GaugeField a)) :
    pushToUnit (c • ν₁ + d • ν₂) = c • pushToUnit ν₁ + d • pushToUnit ν₂ := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsAtEverySpacing.pushToUnit_add_smul <;> assumption
private theorem mem_iff_toUnit_mem (hG : TransportsGibbsMeasures a β) (ν : BorelProb a) :
    ν.1 ∈ periodicGibbsAtMesh a β ↔
      (BorelProb.toUnit ν).1 ∈ periodicGibbsAtMesh 1 β := by
  constructor
  · intro h
    exact ((hG ν).2.2 h.1).1 h
  · intro h
    exact ((hG ν).2.2 ((hG ν).1.2 h.1)).2 h
private theorem pushToUnit_bijOn (e : BorelProb a ≃ₜ BorelProb 1) (he : ∀ ν, e ν = BorelProb.toUnit ν)
    (hG : TransportsGibbsMeasures a β) :
    BijOn pushToUnit (periodicGibbsAtMesh a β) (periodicGibbsAtMesh 1 β) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ν hν
    exact (mem_iff_toUnit_mem hG (probOfMeasure ν hν.1.1)).1 hν
  · intro ν hν ν' hν' h
    have h₁ : e (probOfMeasure ν hν.1.1) = e (probOfMeasure ν' hν'.1.1) := by
      rw [he, he]
      exact Subtype.ext h
    exact congrArg Subtype.val (e.injective h₁)
  · intro ρ hρ
    have hf : BorelProb.toUnit (e.symm (probOfMeasure ρ hρ.1.1)) = probOfMeasure ρ hρ.1.1 := by
      rw [← he]
      exact e.apply_symm_apply _
    refine ⟨(e.symm (probOfMeasure ρ hρ.1.1)).1, (mem_iff_toUnit_mem hG _).2 ?_, ?_⟩
    · rw [hf]
      exact hρ
    · exact congrArg Subtype.val hf
private theorem isExtremeState_iff {𝒢 : Set (Measure (GaugeField a))}
    {𝒢' : Set (Measure (GaugeField 1))} (hb : BijOn pushToUnit 𝒢 𝒢')
    (hc : IsConvexStateSet 𝒢) {ν : Measure (GaugeField a)} (hν : ν ∈ 𝒢) :
    IsExtremeState 𝒢 ν ↔ IsExtremeState 𝒢' (pushToUnit ν) := by
  constructor
  · rintro ⟨-, hext⟩
    refine ⟨hb.mapsTo hν, ?_⟩
    intro ρ₁ hρ₁ ρ₂ hρ₂ t ht ht' hsum
    obtain ⟨ν₁, h₁, rfl⟩ := hb.surjOn hρ₁
    obtain ⟨ν₂, h₂, rfl⟩ := hb.surjOn hρ₂
    have hmix := hc ν₁ h₁ ν₂ h₂ t ht.le ht'.le
    have heq : ν = ENNReal.ofReal t • ν₁ + ENNReal.ofReal (1 - t) • ν₂ :=
      hb.injOn hν hmix (by rw [pushToUnit_linearCombination]; exact hsum)
    obtain ⟨e₁, e₂⟩ := hext ν₁ h₁ ν₂ h₂ t ht ht' heq
    exact ⟨congrArg _ e₁, congrArg _ e₂⟩
  · rintro ⟨-, hext⟩
    refine ⟨hν, ?_⟩
    intro ν₁ h₁ ν₂ h₂ t ht ht' hsum
    obtain ⟨e₁, e₂⟩ := hext _ (hb.mapsTo h₁) _ (hb.mapsTo h₂) t ht ht'
      (by rw [hsum, pushToUnit_linearCombination])
    exact ⟨hb.injOn h₁ hν e₁, hb.injOn h₂ hν e₂⟩
private theorem euclidNorm_eq_euclidNormVec (x : Point) :
    euclidNorm x = TorusMetric.euclidNormVec x := by apply _root_.YangMills.Construction.InfiniteLattice.SymmetryAction.euclidNorm_eq_euclidNormVec <;> assumption
private theorem euclidNorm_sq_eq_euclidDot (x : Point) : euclidNorm x ^ 2 = euclidDot x x := by apply _root_.YangMills.Construction.LatticeConventions.DiagonalPictureExpansion.euclidNorm_sq_eq_selfDot <;> assumption
private theorem mirrorReflections_areMotions (hA : MirrorPositionsAndReflectionRules)
    (hM : SymmetriesTransportLinksSupportsAndPlaquettes) (ha : 0 < a) :
    MirrorReflectionsAreMotions a := by
  intro Q hQ
  obtain ⟨hcoord, hdiag, hdist, -⟩ := hA a ha Q
  have honto : Q.reflect '' (latticeSubgroup a : Set Point) = (latticeSubgroup a : Set Point) := by
    rcases Q.normal_valid with h | h
    · exact (hcoord h).2 (hQ.1 h)
    · exact (hdiag h).2 (hQ.2 h)
  let r : LatticeSymmetry a :=
    ⟨Q.reflect, fun x y => by
      rw [← euclidNorm_eq_euclidNormVec, ← euclidNorm_eq_euclidNormVec]
      exact hdist x y, honto⟩
  rw [← (hM a ha).1.1]
  exact ⟨r, rfl⟩
private theorem hyperplaneReflect_preserves_dist {u : AmbientSpace} (hN : dotProduct u u ≠ 0) (s : ℝ)
    (x y : AmbientSpace) :
    TorusMetric.euclidNormVec (hyperplaneReflect u s x - hyperplaneReflect u s y) =
      TorusMetric.euclidNormVec (x - y) := by apply _root_.YangMills.Construction.InfiniteLattice.euclidNormVec_hyperplaneReflect_sub <;> assumption
private theorem normal_eq_smul_of_motion {u : AmbientSpace} {s : ℝ} (hu : u ≠ 0)
    (hN : dotProduct u u ≠ 0) {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace}
    (hw : w ∈ hyperoctahedralLinearGroup) {v : LatticePoint a}
    (hwv : hyperplaneReflect u s = latticeMotion w v) :
    ∃ (n : Point) (t : ℝ), t ≠ 0 ∧ (IsAxialNormal n ∨ IsFaceDiagonalNormal n) ∧ u = t • n := by
  have hlin : ∀ x, w x = x - (2 * dotProduct u x / dotProduct u u) • u := by
    intro x
    have h₁ := congrFun hwv x
    have h₀ := congrFun hwv 0
    simp only [latticeMotion, map_zero, zero_add] at h₁ h₀
    have hx : w x = hyperplaneReflect u s x - hyperplaneReflect u s 0 := by
      rw [h₁, h₀]
      abel
    rw [hx]
    funext μ
    simp only [hyperplaneReflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dotProduct_zero,
      Pi.zero_apply]
    field_simp
    ring
  obtain ⟨μ, hμ⟩ : ∃ μ, u μ ≠ 0 := by
    by_contra hc
    exact hu (funext fun ν => by_contra fun h => hc ⟨ν, h⟩)
  have hmem : w (Pi.single μ 1) ∈ signedUnitVectors := by
    have hset : w '' signedUnitVectors = signedUnitVectors := hw
    rw [← hset]
    exact mem_image_of_mem w ⟨μ, Or.inl rfl⟩
  obtain ⟨k, hk, hcoord⟩ : ∃ k : ℝ, k ≠ 0 ∧ ∀ ν,
      w (Pi.single μ 1) ν = (Pi.single μ (1 : ℝ) : AmbientSpace) ν - k * u ν := by
    refine ⟨2 * u μ / dotProduct u u, div_ne_zero (mul_ne_zero two_ne_zero hμ) hN, fun ν => ?_⟩
    rw [hlin]
    simp [dotProduct_single]
  obtain ⟨κ, ε, hε, hκ⟩ : ∃ (κ : Fin 4) (ε : ℝ), (ε = 1 ∨ ε = -1) ∧ ∀ ν,
      w (Pi.single μ 1) ν = ε * (Pi.single κ (1 : ℝ) : AmbientSpace) ν := by
    obtain ⟨κ, h | h⟩ := hmem
    · exact ⟨κ, 1, Or.inl rfl, fun ν => by rw [h]; simp⟩
    · exact ⟨κ, -1, Or.inr rfl, fun ν => by rw [h]; simp⟩
  have hrow : ∀ ν, (Pi.single μ (1 : ℝ) : AmbientSpace) ν - k * u ν =
      ε * (Pi.single κ (1 : ℝ) : AmbientSpace) ν :=
    fun ν => (hcoord ν).symm.trans (hκ ν)
  by_cases hκμ : κ = μ
  · subst hκμ
    refine ⟨_root_.YangMills.Construction.LatticeConventions.basisVector κ, u κ, hμ, Or.inl ⟨κ, rfl⟩, ?_⟩
    funext ν
    by_cases hν : ν = κ
    · subst hν
      simp [_root_.YangMills.Construction.LatticeConventions.basisVector]
    · have h := hrow ν
      simp only [Pi.single_eq_of_ne hν, mul_zero, zero_sub, neg_eq_zero, mul_eq_zero, hk,
        false_or] at h
      simp [_root_.YangMills.Construction.LatticeConventions.basisVector, Pi.single_eq_of_ne hν, h]
  · have hμκ : μ ≠ κ := fun h => hκμ h.symm
    have h₁ := hrow μ
    have h₂ := hrow κ
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hμκ, Pi.single_eq_of_ne hκμ, mul_zero,
      mul_one] at h₁ h₂
    have hu : u = u μ • (_root_.YangMills.Construction.LatticeConventions.basisVector μ - ε • _root_.YangMills.Construction.LatticeConventions.basisVector κ) := by
      funext ν
      by_cases hνμ : ν = μ
      · subst hνμ
        simp [_root_.YangMills.Construction.LatticeConventions.basisVector, Pi.single_eq_of_ne hμκ]
      · by_cases hνκ : ν = κ
        · subst hνκ
          simp only [_root_.YangMills.Construction.LatticeConventions.basisVector, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same,
            Pi.single_eq_of_ne hνμ, smul_eq_mul, mul_one, zero_sub]
          refine mul_left_cancel₀ hk ?_
          linear_combination (-1) * h₂ - ε * h₁
        · have h := hrow ν
          simp only [Pi.single_eq_of_ne hνμ, Pi.single_eq_of_ne hνκ, mul_zero, zero_sub,
            neg_eq_zero, mul_eq_zero, hk, false_or] at h
          simp [_root_.YangMills.Construction.LatticeConventions.basisVector, Pi.single_eq_of_ne hνμ, Pi.single_eq_of_ne hνκ, h]
    refine ⟨_root_.YangMills.Construction.LatticeConventions.basisVector μ - ε • _root_.YangMills.Construction.LatticeConventions.basisVector κ, u μ, hμ, Or.inr ⟨μ, κ, hμκ, ?_⟩, hu⟩
    rcases hε with rfl | rfl
    · exact Or.inr (by simp)
    · exact Or.inl (by simp)
private theorem preservingHyperplanes_areMirrors (hA : MirrorPositionsAndReflectionRules)
    (hM : SymmetriesTransportLinksSupportsAndPlaquettes) (ha : 0 < a) :
    LatticePreservingHyperplanesAreMirrors a := by
  intro u s hu hr
  have hN : dotProduct u u ≠ 0 := fun h => hu (dotProduct_self_eq_zero.1 h)
  have hmem : hyperplaneReflect u s ∈ affineHyperoctahedralMaps a := by
    rw [← (hM a ha).1.1]
    exact ⟨⟨hyperplaneReflect u s, hyperplaneReflect_preserves_dist hN s, hr⟩, rfl⟩
  obtain ⟨w, hw, v, hwv⟩ := hmem
  obtain ⟨n, t, ht, hn, rfl⟩ := normal_eq_smul_of_motion hu hN hw hwv
  have hdot : ∀ x : Point, dotProduct (t • n) x = t * euclidDot n x := fun x => by
    simp only [dotProduct, euclidDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => by ring
  have hself : dotProduct (t • n) (t • n) = t * (t * euclidDot n n) := by
    simp only [dotProduct, euclidDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => by ring
  have hnn : euclidDot n n ≠ 0 := by
    intro h
    apply hN
    rw [hself, h]
    simp
  let Q : NormalHyperplane := ⟨n, s / t, hn⟩
  have hrefl : Q.reflect = hyperplaneReflect (t • n) s := by
    funext x
    change x - (2 * (euclidDot n x - s / t) / euclidNorm n ^ 2) • n =
      x - (2 * (dotProduct (t • n) x - s) / dotProduct (t • n) (t • n)) • (t • n)
    rw [euclidNorm_sq_eq_euclidDot, hdot, hself, smul_smul]
    congr 2
    field_simp
  obtain ⟨hcoord, hdiag, -⟩ := hA a ha Q
  have honto : Q.reflect '' (latticeSubgroup a : Set Point) = (latticeSubgroup a : Set Point) := by
    rw [hrefl]
    exact hr
  refine ⟨Q, ⟨fun h => (hcoord h).1 honto, fun h => (hdiag h).1 honto⟩, ?_⟩
  ext x
  change euclidDot n x = s / t ↔ dotProduct (t • n) x = s
  rw [hdot, eq_div_iff ht, mul_comm]
theorem statement_holds (hD : ScalingToUnitSpacing.UnitSpacingTransport)
    (hE : InfiniteLattice.GibbsEquivalences.GibbsEquivalenceStatement)
    (hA : MirrorPositionsAndReflectionRules)
    (hM : SymmetriesTransportLinksSupportsAndPlaquettes) : Statement := by
  intro a β ha hβ
  obtain ⟨-, -, -, -, -, -, -, -, e, he, -⟩ := (hD a ha).1
  have hI := (hD a ha).2.2.1
  have hG := (hD a ha).2.2.2.1 β hβ
  have hb := pushToUnit_bijOn e he hG
  have hconv : IsConvexStateSet (periodicGibbsAtMesh a β) :=
    fun ν₁ h₁ ν₂ h₂ t ht ht' => (hE a β ha hβ).2.2.2 ν₁ ν₂ h₁ h₂ t ht ht'
  have hconv₁ : IsConvexStateSet (periodicGibbsAtMesh 1 β) :=
    fun ν₁ h₁ ν₂ h₂ t ht ht' => (hE 1 β one_pos hβ).2.2.2 ν₁ ν₂ h₁ h₂ t ht ht'
  refine ⟨⟨hb, fun ν₁ _ ν₂ _ t _ _ => pushToUnit_linearCombination _ _ ν₁ ν₂, ?_⟩, fun L K => rfl,
    ⟨hconv, hconv₁, ?_, fun ν hν => isExtremeState_iff hb hconv hν⟩,
    mirrorReflections_areMotions hA hM ha, preservingHyperplanes_areMirrors hA hM ha⟩
  · refine ⟨e.subtype fun ν => ?_, fun ν => ?_⟩
    · change ν.1 ∈ periodicGibbsAtMesh a β ↔ (e ν).1 ∈ periodicGibbsAtMesh 1 β
      rw [he]
      exact mem_iff_toUnit_mem hG ν
    · change (e ν.1).1 = _
      rw [he]
      rfl
  · intro ν hν
    obtain ⟨-, hT, -, -, hrest⟩ := hI (probOfMeasure ν hν.1.1)
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨hT.1 h₁, ((hrest h₁).2.2).1 h₂⟩
    · rintro ⟨h₁, h₂⟩
      have h₁' := hT.2 h₁
      exact ⟨h₁', ((hrest h₁').2.2).2 h₂⟩
end GibbsAtFixedSpacing.PeriodicGibbsUnderRescaling
end
end YangMills.Construction
