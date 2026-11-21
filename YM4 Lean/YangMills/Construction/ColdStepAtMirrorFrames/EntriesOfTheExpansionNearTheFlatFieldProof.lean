import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtANearFlatTopProof
import YangMills.Construction.ColdStepAtMirrorFrames.TransportOfTheExpansionProof
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace ExpansionCoefficientsNearUniformFieldAux
theorem decayWeight_pos (L : ℕ) (δ x : ℝ) : 0 < torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.torusDecayFactor_pos <;> assumption
variable {F : BlockFrame}
theorem decayWeight_mono (L : ℕ) {δ x y : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    torusDecayFactor L δ x ≤ torusDecayFactor L δ y := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ExpansionTransport.torusDecayFactor_mono <;> assumption
theorem bondDeriv_sub_const {j k : ℕ} (G : F.GaugeField j → ℝ) (a : ℝ) (U : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (A : Fin k → imaginaryQuaternions) (hk : 1 ≤ k) :
    bondDeriv (fun V => G V - a) U c A = bondDeriv G U c A := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CentredExpansionNearUniformTopProof.bondDeriv_sub_const <;> assumption
def offsetSupNorm (o : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun l => (o l).natAbs
theorem add_siteOfCoords_siteOffset (hp : ∀ i, F.period F.depth i ≠ 0) (y z : F.Site F.depth) :
    y + siteOfCoords F.depth (siteOffset y z) = z := by
  funext i
  have : NeZero (F.period F.depth i) := ⟨hp i⟩
  show y i + (((z i - y i).valMinAbs : ℤ) : ZMod (F.period F.depth i)) = z i
  rw [ZMod.coe_valMinAbs]
  ring
theorem siteSupDist_eq_offsetSupNorm (hp : ∀ i, F.period F.depth i ≠ 0) (y z : F.Site F.depth) :
    siteSupDist y z = offsetSupNorm (siteOffset y z) := by
  unfold siteSupDist offsetSupNorm
  congr 1
  funext i
  have : NeZero (F.period F.depth i) := ⟨hp i⟩
  show (y i - z i).valMinAbs.natAbs = (z i - y i).valMinAbs.natAbs
  rw [← neg_sub (z i) (y i), ZMod.natAbs_valMinAbs_neg]
end ExpansionCoefficientsNearUniformFieldAux
open ExpansionCoefficientsNearUniformFieldAux
theorem expansionTermsNearUniformField_holds (hrow : UniformFieldDerivComparison) :
    ExpansionCoefficientsNearUniformField := by
  obtain ⟨C₀, hC₀, hr⟩ := hrow
  refine ⟨C₀, hC₀, ?_⟩
  intro L t n₀ σ δ E E₃ f F T y W B r k c A hf hF hδ hE hEE hT hW hfl hag hk1 hk2 hA
  have hp : ∀ i, F.period F.depth i ≠ 0 := fun i => by have := hag.1 i; omega
  have hE3 : 0 ≤ E₃ := hE.trans hEE
  have hextra : 0 ≤ C₀ * E₃ * ∑ b ∈ T, ‖B b.1 b.2‖ := by positivity
  have hG := decayWeight_pos L δ (r : ℝ)
  let h : Fin k → (Fin 4 → ℤ) × Fin 4 := fun l => (siteOffset y (c l).1, (c l).2)
  have hbf : bondsAt y h = c := by
    funext l
    show (y + siteOfCoords F.depth (siteOffset y (c l).1), (c l).2) = c l
    rw [add_siteOfCoords_siteOffset hp]
  by_cases hb : ∀ l, BondWithinRadius r (h l)
  · have := hr L t n₀ σ δ E E₃ f F T y W B r k h A hf hF hδ hE hEE hT hW hfl hag hk2 hb hA
    rw [hbf] at this
    refine this.trans (add_le_add_left ?_ _)
    gcongr
    linarith
  · push Not at hb
    obtain ⟨l, hl⟩ := hb
    have hfar : r ≤ bondSpan y c := by
      by_contra hcon
      have h1 : siteSupDist y (c l).1 ≤ bondSpan y c :=
        le_trans (Finset.le_sup (f := fun l : Fin k => siteSupDist y (c l).1) (Finset.mem_univ l)) (le_max_left _ _)
      have h2 : offsetSupNorm (siteOffset y (c l).1) < r := by
        rw [← siteSupDist_eq_offsetSupNorm hp]
        omega
      apply hl
      have hc : ∀ m, ((siteOffset y (c l).1 m).natAbs) ≤ offsetSupNorm (siteOffset y (c l).1) := fun m =>
        Finset.le_sup (f := fun m => (siteOffset y (c l).1 m).natAbs) (Finset.mem_univ m)
      refine ⟨fun m => ?_, fun m => ?_⟩
      · have := hc m
        show |siteOffset y (c l).1 m| ≤ (r : ℤ)
        rw [abs_le]
        omega
      · have := hc m
        show |((siteOffset y (c l).1 + Pi.single (c l).2 1 : Fin 4 → ℤ)) m| ≤ (r : ℤ)
        rw [abs_le]
        by_cases e : m = (c l).2
        · subst e
          simp only [Pi.add_apply, Pi.single_eq_same]
          omega
        · simp only [Pi.add_apply, Pi.single_eq_of_ne e, add_zero]
          omega
    have huni : IsSmallCurvature σ (uniformField F F.depth) := by
      have := hfl 0 le_rfl zero_le_one
      have e0 : expFlow B (uniformField F F.depth) 0 = uniformField F F.depth := by
        have h1 : expUnit 0 = 1 := by
          apply Subtype.ext
          show NormedSpace.exp (((0 : imaginaryQuaternions)) : Quaternion ℝ) = 1
          simp
        funext y' i
        simp [expFlow, leftTranslate, h1]
      rwa [e0] at this
    have hGs : torusDecayFactor L δ r ≤ torusDecayFactor L δ (bondSpan y c) :=
      decayWeight_mono L hδ (by positivity) (by exact_mod_cast hfar)
    have bound : ∀ U : F.GaugeField F.depth, IsSmallCurvature σ U →
        |bondDeriv (subtractTrivial f F y) U c A| ≤ E / torusDecayFactor L δ r := by
      intro U hU
      have e1 : bondDeriv (subtractTrivial f F y) U c A = bondDeriv (f F y) U c A :=
        bondDeriv_sub_const (f F y) _ U c A hk1
      rw [e1]
      have a := hf.decay F hF y U k c A hU hk1 (by omega) hA
      rw [if_neg (by omega : k ≠ 3)] at a
      exact a.trans (div_le_div_of_nonneg_left hE hG hGs)
    have a1 := bound W hW
    have a2 := bound _ huni
    have a3 := abs_sub (bondDeriv (subtractTrivial f F y) W c A)
      (bondDeriv (subtractTrivial f F y) (uniformField F F.depth) c A)
    have e : 3 * E / torusDecayFactor L δ r =
        E / torusDecayFactor L δ r + E / torusDecayFactor L δ r + E / torusDecayFactor L δ r := by
      ring
    have a4 : 0 ≤ E / torusDecayFactor L δ r := by positivity
    rw [e]
    linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
