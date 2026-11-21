import YangMills.Construction.FormsOnATorus.FarEntriesOfACube
import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormOfTheCubeProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped Quaternion
namespace YangMills.Construction.LimitForms
open TorusFields TorusLumps LevelAction RenormalizationStepParameters ColdChain ResponseInTheExpansion WeightedResponses BlockAverages ColdStepAtMirrorFrames
section Sites
variable {n : ℕ} [NeZero n]
private theorem supBall_isRegularRegion (o : TorusSite n) {r : ℕ} (hr : 2048 ≤ r) (hn : 4 * r < n) :
    IsRegularRegion (supBall o (r : ℝ)) 1024 := by apply _root_.YangMills.SharedProofs.p31712 <;> assumption
private theorem trivialField_isColdOn {s : ℝ} (hs : 0 < s) (X : Finset (TorusSite n)) : IsColdOn s X (trivialField n) := by apply _root_.YangMills.SharedProofs.p25190 <;> assumption
private theorem supDist_bondFrom (o : TorusSite n) (b b' : IntBond) (h : ∀ i, 2 * |b.1 i - b'.1 i| < (n : ℤ)) :
    supDist (bondFrom o b).1 (bondFrom o b').1 = bondSupDist b b' := by apply _root_.YangMills.SharedProofs.p76264 <;> assumption
end Sites
section Entries
private def hessianEntry (a : ℝ) (L k : ℕ) {n : ℕ} [NeZero n] (o : TorusSite n) (X : Finset (TorusSite n)) (b b' : IntBond) : ℝ :=
  mixedDeriv (actionAtLevel a L k X) (trivialField n) ![bondFrom o b, bondFrom o b'] ![BoxGaussian.imaginaryUnitI, BoxGaussian.imaginaryUnitI]
private theorem areUnitVectors_imaginaryUnitI : AreUnitVectors ![BoxGaussian.imaginaryUnitI, BoxGaussian.imaginaryUnitI] := by apply _root_.YangMills.SharedProofs.p1192 <;> assumption
private def HessianDecayBound (a δ : ℝ) (L : ℕ) (C : ℝ) : Prop :=
  ∀ (t n : ℕ) [NeZero n] (X : Finset (TorusSite n)) (o : TorusSite n) (b b' : IntBond), 64 ≤ n → IsRegularRegion X 1024 →
    (∀ i, 2 * |b.1 i - b'.1 i| < (n : ℤ)) → |hessianEntry a L t o X b b'| ≤ C * Real.exp (-δ * bondSupDist b b')
private theorem supDist_le_bondListSpread {n : ℕ} [NeZero n] (c : Fin 2 → TorusBond n) : supDist (c 0).1 (c 1).1 ≤ bondListSpread c := by
  unfold bondListSpread
  exact le_trans (Finset.le_sup (f := fun l' => supDist (c 0).1 (c l').1) (Finset.mem_univ 1))
    (Finset.le_sup (f := fun l => Finset.univ.sup fun l' => supDist (c l).1 (c l').1) (Finset.mem_univ 0))
private theorem exists_hessianDecayBound (hA : ActionSmoothAlongMoves) {a δ lam ρ σA cg : ℝ} {L : ℕ} {N : ℕ → ℝ} (ha : 0 < a)
    (hL : Odd L) (hc : ColdChainConstants a δ L lam ρ σA cg N) : ∃ C, 0 < C ∧ HessianDecayBound a δ L C := by
  obtain ⟨C, hC, H⟩ := hA a δ L lam ρ σA cg N ha hL hc
  obtain ⟨hδ, -, -, -, -, hσ, -, -, -⟩ := hc
  refine ⟨C, hC, fun t n _ X o b b' hn hreg hsm => ?_⟩
  have h := (H t n hn X (trivialField n) hreg (trivialField_isColdOn hσ X)).2.1 2 ![bondFrom o b, bondFrom o b'] ![BoxGaussian.imaginaryUnitI, BoxGaussian.imaginaryUnitI]
    (by norm_num) (by norm_num) areUnitVectors_imaginaryUnitI
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le)
  have h2 : bondSupDist b b' ≤ bondListSpread (![bondFrom o b, bondFrom o b'] : Fin 2 → TorusBond n) := by
    rw [← supDist_bondFrom o b b' hsm]
    exact supDist_le_bondListSpread (![bondFrom o b, bondFrom o b'] : Fin 2 → TorusBond n)
  have h5 : (bondSupDist b b' : ℝ) ≤ (bondListSpread (![bondFrom o b, bondFrom o b'] : Fin 2 → TorusBond n) : ℝ) := by
    exact_mod_cast h2
  nlinarith
private theorem eventually_poly_mul_exp_lt (C β : ℝ) (hβ : 0 < β) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m, M ≤ m → C * ((m : ℝ) + 1) ^ 4 * Real.exp (-β * m) < ε := by apply _root_.YangMills.SharedProofs.p56559 <;> assumption
end Entries
theorem offDiagonalDecay_of_actionSmooth (hA : ActionSmoothAlongMoves) : offDiagonalDecayStatement := by
  intro Tb hD
  have hδ := hD.δ₁_pos
  have ha : 0 < Tb.coupling := by linarith [hD.a_ge]
  obtain ⟨C₂, hC₂, hSp⟩ := exists_hessianDecayBound hA ha hD.L_odd hD.chain
  set δ := Tb.δ₁ with hδdef
  obtain ⟨R₂, hR₂⟩ := eventually_poly_mul_exp_lt C₂ (δ / 8) (by linarith) one_pos
  refine ⟨δ / 8, max 1024 R₂, by linarith, fun k n _ o R hR hn b b' hb hb' hfar => ?_⟩
  have hR1 : 1024 ≤ R := le_trans (le_max_left _ _) hR
  have hR2 : R₂ ≤ R := le_trans (le_max_right _ _) hR
  have e2 : ((2 * R : ℕ) : ℝ) = 2 * (R : ℝ) := by push_cast; ring
  have hreg : IsRegularRegion (supBall o ((2 * R : ℕ) : ℝ)) 1024 := supBall_isRegularRegion o (by omega) (by omega)
  have hs := hSp k n (supBall o ((2 * R : ℕ) : ℝ)) o b b' (by omega) hreg (fun i => by
    have a1 := abs_le.mp (hb.1 i)
    have a2 := abs_le.mp (hb'.1 i)
    have : |b.1 i - b'.1 i| ≤ 4 * (R : ℤ) := by
      rw [abs_le]
      push_cast at a1 a2
      constructor <;> omega
    omega)
  unfold hessianEntry at hs
  rw [e2] at hs
  refine hs.trans ?_
  have hd : (R : ℝ) ≤ 4 * bondSupDist b b' := by exact_mod_cast hfar
  have h1 : C₂ * Real.exp (-δ * bondSupDist b b') ≤ C₂ * Real.exp (-(δ / 4) * R) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC₂.le
  have h2 := hR₂ R hR2
  have hP : (1 : ℝ) ≤ ((R : ℝ) + 1) ^ 4 := one_le_pow₀ (by
    have : (0 : ℝ) ≤ R := by positivity
    linarith)
  have h3 : Real.exp (-(δ / 4) * R) = Real.exp (-(δ / 8) * R) * Real.exp (-(δ / 8 * R)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  set e1 := Real.exp (-(δ / 8) * R)
  set e2' := Real.exp (-(δ / 8 * R))
  have he2 : 0 < e2' := Real.exp_pos _
  have h4 : C₂ * e1 ≤ 1 := by
    have : C₂ * e1 ≤ C₂ * ((R : ℝ) + 1) ^ 4 * e1 := by
      have : 0 ≤ C₂ * e1 := by positivity
      nlinarith
    linarith
  calc _ ≤ C₂ * Real.exp (-(δ / 4) * R) := h1
    _ = (C₂ * e1) * e2' := by rw [h3]; ring
    _ ≤ 1 * e2' := mul_le_mul_of_nonneg_right h4 he2.le
    _ = _ := one_mul _
end YangMills.Construction.LimitForms
end
