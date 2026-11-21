import YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
import YangMills.Construction.InfiniteLattice.AllMirrorsOfPeriodicGibbsStates
import YangMills.Construction.VolumeTransfer.FactsOfLatticeSymmetries
import YangMills.Construction.VolumeTransfer.InvarianceOfPeriodicGibbsStates
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.VolumeTransfer.PeriodicGibbsInvariance
open InfiniteLattice
theorem isSymmetricUnder_of_toFun_eq {a : ℝ} {μ : Measure (GaugeField a)}
    {g g' : LatticeSymmetry a} (h : g.toFun = g'.toFun) (hg : IsSymmetricUnder μ g) :
    IsSymmetricUnder μ g' := by
  cases g
  cases g'
  subst h
  exact hg
theorem shift_mem_latticeMotions {a : ℝ} (v : LatticePoint a) :
    (shift v).toFun ∈ latticeMotions a :=
  ⟨LinearMap.id, ⟨1, fun _ => Or.inl rfl⟩, v, v.2, fun _ => rfl⟩
theorem realNormal_axial_dotProduct (i : Fin 4) (x : AmbientSpace) :
    (ReflectionClass.axial i).realNormal ⬝ᵥ x = x i := by
  simp [ReflectionClass.realNormal, ReflectionClass.intNormal, dotProduct, Pi.single_apply]
theorem realNormal_axial (i : Fin 4) :
    (ReflectionClass.axial i).realNormal = basisVector i := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.realNormal_axial <;> assumption
theorem symmetry_mem_latticeMotions {a : ℝ} (H : LatticeMirror a) {i : Fin 4}
    (hH : H.cls = ReflectionClass.axial i) :
    H.symmetry.toFun ∈ latticeMotions a := by
  obtain ⟨F, c, hc⟩ := H
  obtain rfl : F = ReflectionClass.axial i := hH
  obtain ⟨q, rfl⟩ := hc
  have ht : ((2 * ((q : ℝ) * (a / 2))) • basisVector i : AmbientSpace) ∈ latticeSubgroup a := by
    refine ⟨fun j => if j = i then q else 0, fun j => ?_⟩
    by_cases h : j = i
    · subst h
      simp [basisVector]
      ring
    · simp [basisVector, h]
  refine ⟨coordinateSignFlip i, coordinateSignFlip_mem_hypercubicGroup i, _, ht, fun x => ?_⟩
  rw [← coordinateReflection_eq_signFlip_add]
  change hyperplaneReflect (ReflectionClass.axial i).realNormal _ x = _
  rw [hyperplaneReflect, ReflectionClass.realNormal_dot_axial, realNormal_axial_dotProduct,
    realNormal_axial, coordinateReflection]
  simp
theorem mem_latticeMotions_of_isReflectionTranslation {L K : ℕ} {r : AmbientSpace → AmbientSpace}
    (hr : (LatticeGeometry.euclidean L K).IsReflectionTranslation r) :
    r ∈ latticeMotions (refinedSpacing L K) := by
  obtain ⟨ε, t, ht, h⟩ := hr
  refine ⟨frameLinearMap (1, ε), frameLinearMap_mem_hypercubicGroup _, t, ht, fun x => ?_⟩
  have hx : r x = LatticeGeometry.diagSign ε x + t := h x
  rw [hx]
  congr 1
theorem holds (hAll : PeriodicGibbsSymmetries.Statement)
    (hFacts : ReflectionTranslationFacts) : Statement := by
  intro L hL K β hβ μ _ hμ
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have ha : 0 < refinedSpacing L (K : ℕ) := by
    have : (0 : ℝ) < L := by exact_mod_cast hL0
    simp only [refinedSpacing, PeriodicLattice.meshSize]
    positivity
  have hμ' : IsPeriodicGibbs β μ := hμ
  have hmot : PeriodicGibbsSymmetries.IsMotionInvariant μ :=
    ((hAll _ ha β hβ).1 μ hμ').1
  obtain ⟨-, -, -, -, hcube, -, hagree⟩ := hFacts L hL K
  refine ⟨hμ'.1, ⟨hmot, fun v => ?_, ?_⟩, fun lc hlc => ?_⟩
  · exact isSymmetricUnder_of_toFun_eq rfl (hmot ⟨_, shift_mem_latticeMotions v⟩)
  · rintro H ⟨i, hH⟩
    exact isSymmetricUnder_of_toFun_eq rfl (hmot ⟨_, symmetry_mem_latticeMotions H hH⟩)
  · obtain ⟨⟨k, hk⟩, -, hgroup⟩ := (hcube lc hlc).1
    have hlc' : lc = k * refinedSpacing L (K : ℕ) := (div_eq_iff ha.ne').mp hk
    refine ⟨fun i ι => ?_, fun r hr => ?_⟩
    · refine ⟨⟨ReflectionClass.axial i, ι * lc - 1 / 2 * refinedSpacing L (K : ℕ),
        ⟨2 * ι * k - 1, ?_⟩⟩, rfl, ?_, ⟨ι * k - 1, ?_⟩⟩
      · rw [hlc']
        push_cast
        ring
      · ext x
        simp only [LatticeMirror.plane, Set.mem_ofPred_eq, realNormal_axial_dotProduct,
          FaceReflections.faceHyperplane]
      · change ι * lc - 1 / 2 * refinedSpacing L (K : ℕ) = _
        rw [hlc']
        push_cast
        ring
    · have hs := (hgroup r hr).2
      have hinv := hmot ⟨_, mem_latticeMotions_of_isReflectionTranslation hs⟩
      exact ⟨⟨_, rfl, hinv⟩, hs, ((hagree.1 μ _ hs).2 _ rfl).2 hinv⟩
end YangMills.Construction.VolumeTransfer.PeriodicGibbsInvariance
end
