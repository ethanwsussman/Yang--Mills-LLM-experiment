import YangMills.Construction.Torus.LiftsAndInducedMapsProof
import YangMills.Construction.TwoPoints.FormAtRiemannSumsIsADoubleRiemannSumProof
import YangMills.Construction.TwoPoints.ApproximateIdentitiesAndTheirTranslates
import YangMills.Construction.TwoPoints.FirstConsequencesOfThreeProperties
import YangMills.Construction.TwoPoints.LimitAtApproximateIdentitiesIsEvenAndInvariant
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology ContDiff
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
namespace MollifierLimitSymmetric
def addShift (v : AmbientSpace) : Equiv.Perm AmbientSpace := Equiv.addRight v
theorem addShift_mem_euclideanMotions (v : AmbientSpace) : addShift v ∈ euclideanMotions := by apply _root_.YangMills.Construction.TwoPoints.GridSumForm.addRight_mem_euclideanMotions <;> assumption
theorem actOn_addShift {E : Type*} (v : AmbientSpace) (f : AmbientSpace → E) :
    actOn (addShift v) f = translateFun v f := by
  funext x
  have hinv : (addShift v)⁻¹ x = x - v := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    simp [addShift]
  simp only [actOn, translateFun, Function.comp, hinv]
theorem translateFun_neg_translateFun {E : Type*} (v : AmbientSpace) (f : AmbientSpace → E) :
    translateFun (-v) (translateFun v f) = f := by
  funext x
  simp [translateFun]
theorem mem_euclideanMotions_of_mem_hyperoctahedral {g : Equiv.Perm AmbientSpace}
    (hg : g ∈ hyperoctahedralPerms) : g ∈ euclideanMotions :=
  ⟨g, hg, 0, fun _ => (add_zero _).symm⟩
theorem euclidNorm_apply_of_mem {g : Equiv.Perm AmbientSpace} (hg : g ∈ hyperoctahedralPerms)
    (x : AmbientSpace) : euclidNorm (g x) = euclidNorm x := by apply _root_.YangMills.Construction.TorusLifts.LiftsAndDescendedMaps.euclidNormVec_hyperoctahedral <;> assumption
theorem apply_ne_zero_of_mem {g : Equiv.Perm AmbientSpace} (hg : g ∈ hyperoctahedralPerms)
    {ξ : AmbientSpace} (hξ : ξ ≠ 0) : g ξ ≠ 0 := by
  obtain ⟨L, hL, -⟩ := exists_isSignedPerm hg
  have hzero : g 0 = 0 := by
    rw [← hL, map_zero]
  exact fun h => hξ (g.injective (h.trans hzero.symm))
theorem actOn_translateFun {E : Type*} {g : Equiv.Perm AmbientSpace}
    (hg : g ∈ hyperoctahedralPerms) (ξ : AmbientSpace) (f : AmbientSpace → E) :
    actOn g (translateFun ξ f) = translateFun (g ξ) (actOn g f) := by
  funext x
  obtain ⟨L, hL, -⟩ := exists_isSignedPerm (hyperoctahedralPerms.inv_mem hg)
  have hL' : ∀ y, g⁻¹ y = L y := fun y => (congrFun hL y).symm
  have hsub : g⁻¹ (x - g ξ) = g⁻¹ x - ξ := by
    rw [hL', hL', map_sub, ← hL' (g ξ)]
    simp
  simp only [actOn, translateFun, Function.comp, hsub]
theorem isMollifierSeq_actOn (hF : AdmissibleFormConsequences.Statement)
    (sc : FixedScale) {g : Equiv.Perm AmbientSpace} (hg : g ∈ hyperoctahedralPerms)
    {ρ : ℕ → AmbientSpace → ℂ} (hρ : IsMollifierSeq ρ) :
    IsMollifierSeq fun n => actOn g (ρ n) := by
  intro n hn
  have hρn := hρ n hn
  have hcc : ρ n ∈ ccInfIn (euclidOpenBall (0 : AmbientSpace) (1 / (n : ℝ))) := hρn.1.1
  have hC1 : ρ n ∈ compactC1Complex := ⟨hcc.1.of_le (mod_cast le_top), hcc.2.1, subset_univ _⟩
  obtain ⟨hk, hint, hsupp⟩ := ((hF.2.2.2.1 sc).1 (ρ n) hC1).2.2.1 g hg
  obtain ⟨L, hL, -⟩ := exists_isSignedPerm (hyperoctahedralPerms.inv_mem hg)
  have hsmooth : ContDiff ℝ ∞ (actOn g (ρ n)) := by
    have hcomp : actOn g (ρ n) = ρ n ∘ ⇑L := by
      rw [hL]
      rfl
    rw [hcomp]
    exact hcc.1.comp (LinearMap.toContinuousLinearMap L).contDiff
  have hball : tsupport (actOn g (ρ n)) ⊆ euclidOpenBall (0 : AmbientSpace) (1 / (n : ℝ)) := by
    rw [hsupp]
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hcc.2.2 hx
    simp only [euclidOpenBall, mem_ofPred_eq, sub_zero] at hx' ⊢
    rwa [euclidNorm_apply_of_mem hg]
  exact ⟨⟨⟨hsmooth, hk.mem.2.1, hball⟩, fun x => hρn.1.2 _⟩, fun x => hρn.2.1 _,
    hint.trans hρn.2.2⟩
theorem eventually_real_disjoint_pair (hB : MollifierTranslatesDisjoint.Statement)
    {ξ : AmbientSpace} (hξ : ξ ≠ 0) {ρ : ℕ → AmbientSpace → ℂ} (hρ : IsMollifierSeq ρ) :
    ∀ᶠ n : ℕ in atTop, ρ n ∈ compactC1Real ∧ translateFun ξ (ρ n) ∈ compactC1Real ∧
      DisjointSupports (ρ n) (translateFun ξ (ρ n)) := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
    (2 / euclidNorm ξ)] with n hn
  exact hB.2 ξ hξ ρ hρ n hn
end MollifierLimitSymmetric
open MollifierLimitSymmetric in
theorem MollifierLimitSymmetric.proof
    (hB : MollifierTranslatesDisjoint.Statement)
    (hF : AdmissibleFormConsequences.Statement) :
    MollifierLimitSymmetric.Statement := by
  intro sc S hS hP K hK ξ hξ
  have hinv := hP.invariantPositive.1
  obtain ⟨ρ, hρ⟩ := hB.1
  have hev := eventually_real_disjoint_pair hB hξ hρ
  refine ⟨?_, fun g hg => ?_⟩
  · have hξ' : -ξ ≠ 0 := neg_ne_zero.2 hξ
    have heq : (fun n => S (ρ n) (translateFun (-ξ) (ρ n))) =ᶠ[atTop]
        fun n => S (ρ n) (translateFun ξ (ρ n)) := by
      filter_upwards [hev, eventually_real_disjoint_pair hB hξ' hρ] with n h h'
      obtain ⟨a, b, c⟩ := h
      obtain ⟨-, b', c'⟩ := h'
      have hr := hinv (addShift (-ξ)) (addShift_mem_euclideanMotions _) _ a _ b c
      rw [actOn_addShift, actOn_addShift, translateFun_neg_translateFun] at hr
      rw [hS.1 _ a _ b' c', hr]
    exact tendsto_nhds_unique ((hK _ hξ' ρ hρ).congr' heq) (hK ξ hξ ρ hρ)
  · have hρ' := isMollifierSeq_actOn hF sc hg hρ
    have heq : (fun n => S (actOn g (ρ n)) (translateFun (g ξ) (actOn g (ρ n))))
        =ᶠ[atTop] fun n => S (ρ n) (translateFun ξ (ρ n)) := by
      filter_upwards [hev] with n h
      obtain ⟨a, b, c⟩ := h
      have hr := hinv g (mem_euclideanMotions_of_mem_hyperoctahedral hg) _ a _ b c
      rwa [actOn_translateFun hg] at hr
    exact tendsto_nhds_unique ((hK _ (apply_ne_zero_of_mem hg hξ) _ hρ').congr' heq)
      (hK ξ hξ ρ hρ)
end YangMills.Construction.TwoPoints
end
