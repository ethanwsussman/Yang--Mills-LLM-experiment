import YangMills.Construction.FreeEnergiesOfTheFlow.MeansGivenAStateReadTheCasesProof
import YangMills.Construction.ResponseInTheExpansion.RemainderOfTheResponseReturnsProof
import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficientProof
import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.LawInAState.HatsSumToTheFreeKernelProof
import YangMills.Construction.LawInAState.MarkAtACurvedField
import YangMills.Construction.LawInAState.MarksOnTheBox
import YangMills.Construction.LawInAState.SizesOfALeastWeight
import YangMills.Construction.LawInAState.TheNumbersOfTheChainAreNearOne
import YangMills.Construction.ResponseInTheExpansion.SizeOfTheLocalChainProof
import YangMills.Construction.ResponseInTheExpansion.TheCurvatureIsTheDescendedFormProof
import YangMills.Construction.ResponseInTheExpansion.WeightsExtendToATorus
import YangMills.Construction.ResponseInTheExpansion.WeightsOnTwoTori
import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadiusProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StateLaws
open TorusFields TorusLumps TorusMirror RenormalizationStepParameters StepReturn WeightedResponses ResponseInTheExpansion BoxMarks
open BlockAverages hiding unitStep
open BoxResponses BoxGaussian LumpContours GaugeFixing
open InfiniteLattice (AmbientSpace)
open Classical
section Transplant
variable {N M : ℕ} [NeZero N] [NeZero M]
private theorem valMinAbs_cast_eq {M : ℕ} [NeZero M] {c : ℤ} (h : 2 * |c| < (M : ℤ)) : (((c : ℤ) : ZMod M)).valMinAbs = c := by apply _root_.YangMills.SharedProofs.p9640 <;> assumption
private theorem abs_valMinAbs_sub_le {n : ℕ} [NeZero n] {x y : TorusSite n} {r : ℕ} (h : _root_.YangMills.Construction.TorusFields.supDist x y ≤ r) (i : Fin 4) :
    |(x i - y i).valMinAbs| ≤ (r : ℤ) := by
  have := (_root_.YangMills.Construction.TorusFields.supDist_le_iff x y r).mp h i
  rw [Int.abs_eq_natAbs]
  exact_mod_cast this
private def transplantSite (y : TorusSite N) (z : TorusSite M) : TorusSite N := y + siteOfInt fun i => (z i).valMinAbs
private def returnSite (y w : TorusSite N) : TorusSite M := siteOfInt fun i => (w i - y i).valMinAbs
private theorem abs_valMinAbs_le_of_supDist {r : ℕ} {z : TorusSite M} (h : _root_.YangMills.Construction.TorusFields.supDist z 0 ≤ r) (i : Fin 4) : |(z i).valMinAbs| ≤ (r : ℤ) := by
  simpa using abs_valMinAbs_sub_le h i
private theorem transplantSite_add_unitStep {r : ℕ} (hM : 2 * (r + 1) < M) (y : TorusSite N) {z : TorusSite M} (h : _root_.YangMills.Construction.TorusFields.supDist z 0 ≤ r) (i : Fin 4) :
    transplantSite y (z + unitStep M i) = transplantSite y z + unitStep N i := by
  funext j
  simp only [transplantSite, siteOfInt, Pi.add_apply]
  by_cases hj : j = i
  · subst hj
    have hc := abs_valMinAbs_le_of_supDist h j
    have h1 : z j + unitStep M j j = (((z j).valMinAbs + 1 : ℤ) : ZMod M) := by
      simp [unitStep, ZMod.coe_valMinAbs]
    have h2 : 2 * |(z j).valMinAbs + 1| < (M : ℤ) := by
      have := abs_le.mp hc
      have h3 : |(z j).valMinAbs + 1| ≤ (r : ℤ) + 1 := abs_le.mpr ⟨by omega, by omega⟩
      omega
    rw [h1, valMinAbs_cast_eq h2]
    simp [unitStep]
    ring
  · have h1 : (unitStep M i : TorusSite M) j = 0 := by simp [unitStep, hj]
    have h2 : (unitStep N i : TorusSite N) j = 0 := by simp [unitStep, hj]
    simp [h1, h2]
private theorem returnSite_add_unitStep {r : ℕ} (hN : 2 * (r + 1) < N) (y : TorusSite N) {w : TorusSite N} (h : _root_.YangMills.Construction.TorusFields.supDist w y ≤ r) (i : Fin 4) :
    (returnSite y (w + unitStep N i) : TorusSite M) = returnSite y w + unitStep M i := by
  funext j
  simp only [returnSite, siteOfInt, Pi.add_apply]
  by_cases hj : j = i
  · subst hj
    have hc := abs_valMinAbs_sub_le h j
    have h1 : w j + unitStep N j j - y j = (((w j - y j).valMinAbs + 1 : ℤ) : ZMod N) := by
      simp [unitStep, ZMod.coe_valMinAbs]
      ring
    have h2 : 2 * |(w j - y j).valMinAbs + 1| < (N : ℤ) := by
      have := abs_le.mp hc
      have h3 : |(w j - y j).valMinAbs + 1| ≤ (r : ℤ) + 1 := abs_le.mpr ⟨by omega, by omega⟩
      omega
    rw [h1, valMinAbs_cast_eq h2]
    simp [unitStep]
  · have h1 : (unitStep M i : TorusSite M) j = 0 := by simp [unitStep, hj]
    have h2 : (unitStep N i : TorusSite N) j = 0 := by simp [unitStep, hj]
    simp [h1, h2]
private theorem transplantSite_returnSite {r : ℕ} (hM : 2 * r < M) (y : TorusSite N) {w : TorusSite N} (h : _root_.YangMills.Construction.TorusFields.supDist w y ≤ r) :
    transplantSite y (returnSite y w : TorusSite M) = w := by
  funext j
  have hc := abs_valMinAbs_sub_le h j
  have h2 : 2 * |(w j - y j).valMinAbs| < (M : ℤ) := by omega
  simp only [transplantSite, returnSite, siteOfInt, Pi.add_apply]
  rw [valMinAbs_cast_eq h2, ZMod.coe_valMinAbs]
  ring
private theorem returnSite_transplantSite {r : ℕ} (hN : 2 * r < N) (y : TorusSite N) {z : TorusSite M} (h : _root_.YangMills.Construction.TorusFields.supDist z 0 ≤ r) :
    (returnSite y (transplantSite y z) : TorusSite M) = z := by
  funext j
  have hc := abs_valMinAbs_le_of_supDist h j
  have h2 : 2 * |(z j).valMinAbs| < (N : ℤ) := by omega
  simp only [transplantSite, returnSite, siteOfInt, Pi.add_apply, add_sub_cancel_left]
  rw [valMinAbs_cast_eq h2, ZMod.coe_valMinAbs]
private theorem supDist_transplantSite {r : ℕ} (hN : 2 * r < N) (y : TorusSite N) {z : TorusSite M} (h : _root_.YangMills.Construction.TorusFields.supDist z 0 ≤ r) :
    _root_.YangMills.Construction.TorusFields.supDist (transplantSite y z) y = _root_.YangMills.Construction.TorusFields.supDist z 0 := by
  unfold TorusFields.supDist
  congr 1
  funext j
  have hc := abs_valMinAbs_le_of_supDist h j
  have h2 : 2 * |(z j).valMinAbs| < (N : ℤ) := by omega
  simp only [transplantSite, siteOfInt, Pi.add_apply, add_sub_cancel_left, Pi.zero_apply, sub_zero]
  rw [valMinAbs_cast_eq h2]
private theorem supDist_returnSite {r : ℕ} (hM : 2 * r < M) (y : TorusSite N) {w : TorusSite N} (h : _root_.YangMills.Construction.TorusFields.supDist w y ≤ r) :
    _root_.YangMills.Construction.TorusFields.supDist (returnSite y w : TorusSite M) 0 = _root_.YangMills.Construction.TorusFields.supDist w y := by
  unfold TorusFields.supDist
  congr 1
  funext j
  have hc := abs_valMinAbs_sub_le h j
  have h2 : 2 * |(w j - y j).valMinAbs| < (M : ℤ) := by omega
  simp only [returnSite, siteOfInt, Pi.zero_apply, sub_zero]
  rw [valMinAbs_cast_eq h2]
private def transplantFace (y : TorusSite N) (q : TorusPlaquette M) : TorusPlaquette N := (transplantSite y q.1, q.2)
private def returnFace (y : TorusSite N) (p : TorusPlaquette N) : TorusPlaquette M := (returnSite y p.1, p.2)
private theorem mem_supBall_natCast {n : ℕ} [NeZero n] {o z : TorusSite n} {r : ℕ} : z ∈ supBall o (r : ℝ) ↔ _root_.YangMills.Construction.TorusFields.supDist z o ≤ r := by
  simp [supBall]
private theorem mem_plaquettesIn' {n : ℕ} [NeZero n] {S : Finset (TorusSite n)} {p : TorusPlaquette n} :
    p ∈ plaquettesIn S ↔ p.2.1 < p.2.2 ∧ ∀ z ∈ plaquetteVertices p.1 p.2.1 p.2.2, z ∈ S := by apply _root_.YangMills.Construction.TorusLumps.mem_plaquettesIn_iff_forall_vertex <;> assumption
private theorem supDist_corner_of_mem {n : ℕ} [NeZero n] {o : TorusSite n} {r : ℕ} {p : TorusPlaquette n} (h : p ∈ plaquettesIn (supBall o (r : ℝ))) :
    _root_.YangMills.Construction.TorusFields.supDist p.1 o ≤ r :=
  mem_supBall_natCast.mp ((mem_plaquettesIn'.mp h).2 _ (by simp [plaquetteVertices]))
private theorem supDist_vertices_of_mem {n : ℕ} [NeZero n] {o : TorusSite n} {r : ℕ} {p : TorusPlaquette n} (h : p ∈ plaquettesIn (supBall o (r : ℝ))) :
    _root_.YangMills.Construction.TorusFields.supDist (p.1 + unitStep n p.2.1) o ≤ r ∧ _root_.YangMills.Construction.TorusFields.supDist (p.1 + unitStep n p.2.2) o ≤ r ∧ _root_.YangMills.Construction.TorusFields.supDist (p.1 + unitStep n p.2.1 + unitStep n p.2.2) o ≤ r := by
  have h1 := (mem_plaquettesIn'.mp h).2
  exact ⟨mem_supBall_natCast.mp (h1 _ (by simp [plaquetteVertices])), mem_supBall_natCast.mp (h1 _ (by simp [plaquetteVertices])),
    mem_supBall_natCast.mp (h1 _ (by simp [plaquetteVertices]))⟩
private theorem transplantFace_mem {R : ℕ} (hM : 2 * (R + 1) < M) (hN : 2 * R < N) (y : TorusSite N) {q : TorusPlaquette M}
    (h : q ∈ plaquettesIn (supBall (0 : TorusSite M) (R : ℝ))) : transplantFace y q ∈ plaquettesIn (supBall y (R : ℝ)) := by
  obtain ⟨c1, c2, c3⟩ := supDist_vertices_of_mem h
  have c0 := supDist_corner_of_mem h
  refine mem_plaquettesIn'.mpr ⟨(mem_plaquettesIn'.mp h).1, ?_⟩
  have e1 := transplantSite_add_unitStep hM y c0 q.2.1
  have e2 := transplantSite_add_unitStep hM y c0 q.2.2
  have e3 := transplantSite_add_unitStep hM y c1 q.2.2
  intro z hz
  simp only [transplantFace, plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
  refine mem_supBall_natCast.mpr ?_
  rcases hz with rfl | rfl | rfl | rfl
  · rw [supDist_transplantSite hN y c0]
    exact c0
  · rw [← e1, supDist_transplantSite hN y c1]
    exact c1
  · rw [← e2, supDist_transplantSite hN y c2]
    exact c2
  · rw [← e1, ← e3, supDist_transplantSite hN y c3]
    exact c3
private theorem returnFace_mem {R : ℕ} (hM : 2 * R < M) (hN : 2 * (R + 1) < N) (y : TorusSite N) {p : TorusPlaquette N}
    (h : p ∈ plaquettesIn (supBall y (R : ℝ))) : (returnFace y p : TorusPlaquette M) ∈ plaquettesIn (supBall (0 : TorusSite M) (R : ℝ)) := by
  obtain ⟨c1, c2, c3⟩ := supDist_vertices_of_mem h
  have c0 := supDist_corner_of_mem h
  refine mem_plaquettesIn'.mpr ⟨(mem_plaquettesIn'.mp h).1, ?_⟩
  have e1 : (returnSite y (p.1 + unitStep N p.2.1) : TorusSite M) = returnSite y p.1 + unitStep M p.2.1 := returnSite_add_unitStep hN y c0 p.2.1
  have e2 : (returnSite y (p.1 + unitStep N p.2.2) : TorusSite M) = returnSite y p.1 + unitStep M p.2.2 := returnSite_add_unitStep hN y c0 p.2.2
  have e3 : (returnSite y (p.1 + unitStep N p.2.1 + unitStep N p.2.2) : TorusSite M) = returnSite y (p.1 + unitStep N p.2.1) + unitStep M p.2.2 :=
    returnSite_add_unitStep hN y c1 p.2.2
  intro z hz
  simp only [returnFace, plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
  refine mem_supBall_natCast.mpr ?_
  rcases hz with rfl | rfl | rfl | rfl
  · rw [supDist_returnSite hM y c0]
    exact c0
  · rw [← e1, supDist_returnSite hM y c1]
    exact c1
  · rw [← e2, supDist_returnSite hM y c2]
    exact c2
  · rw [← e1, ← e3, supDist_returnSite hM y c3]
    exact c3
private theorem transplantFace_returnFace {R : ℕ} (hM : 2 * R < M) (y : TorusSite N) {p : TorusPlaquette N} (h : p ∈ plaquettesIn (supBall y (R : ℝ))) :
    transplantFace y (returnFace y p : TorusPlaquette M) = p := by
  simp only [transplantFace, returnFace]
  rw [transplantSite_returnSite hM y (supDist_corner_of_mem h)]
private theorem returnFace_transplantFace {R : ℕ} (hN : 2 * R < N) (y : TorusSite N) {q : TorusPlaquette M}
    (h : q ∈ plaquettesIn (supBall (0 : TorusSite M) (R : ℝ))) : (returnFace y (transplantFace y q) : TorusPlaquette M) = q := by
  simp only [transplantFace, returnFace]
  rw [returnSite_transplantSite hN y (supDist_corner_of_mem h)]
private theorem sum_filter_transplant {R : ℕ} (hM : 2 * (R + 1) < M) (hN : 2 * (R + 1) < N) (y : TorusSite N) (e : Fin 4 × Fin 4 → Prop) [DecidablePred e]
    (G : TorusPlaquette N → ℝ) :
    ∑ p ∈ (plaquettesIn (supBall y (R : ℝ))).filter (fun p => e p.2), G p =
      ∑ q ∈ (plaquettesIn (supBall (0 : TorusSite M) (R : ℝ))).filter (fun q => e q.2), G (transplantFace y q) := by
  refine Finset.sum_bij' (fun p _ => (returnFace y p : TorusPlaquette M)) (fun q _ => transplantFace y q) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨returnFace_mem (by omega) hN y h1, h2⟩
  · intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨transplantFace_mem hM (by omega) y h1, h2⟩
  · intro p hp
    exact transplantFace_returnFace (by omega) y (Finset.mem_filter.mp hp).1
  · intro q hq
    exact returnFace_transplantFace (by omega) y (Finset.mem_filter.mp hq).1
  · intro p hp
    rw [transplantFace_returnFace (by omega) y (Finset.mem_filter.mp hp).1]
private def transplantKernel (y : TorusSite N) (R : ℕ) (κ : TorusPlaquette M → TorusPlaquette M → ℝ) (p p' : TorusPlaquette N) : ℝ :=
  if p ∈ plaquettesIn (supBall y (R : ℝ)) ∧ p' ∈ plaquettesIn (supBall y (R : ℝ)) then
    (1 / 2) * (κ (returnFace y p) (returnFace y p') + κ (returnFace y p') (returnFace y p))
  else 0
private theorem transplantKernel_symm (y : TorusSite N) (R : ℕ) (κ : TorusPlaquette M → TorusPlaquette M → ℝ) (p p' : TorusPlaquette N) :
    transplantKernel y R κ p p' = transplantKernel y R κ p' p := by
  unfold transplantKernel
  by_cases h : p ∈ plaquettesIn (supBall y (R : ℝ)) ∧ p' ∈ plaquettesIn (supBall y (R : ℝ))
  · rw [if_pos h, if_pos h.symm]
    ring
  · rw [if_neg h, if_neg fun h' => h h'.symm]
private theorem abs_transplantKernel_le {R : ℕ} (hM : 2 * R < M) (y : TorusSite N) (κ : TorusPlaquette M → TorusPlaquette M → ℝ) {C c : ℝ} (hC : 0 ≤ C)
    (hκ : ∀ q q', |κ q q'| ≤ C * Real.exp (-(c * max (supDist q.1 (0 : TorusSite M) : ℝ) (supDist q'.1 (0 : TorusSite M) : ℝ))))
    (p p' : TorusPlaquette N) : |transplantKernel y R κ p p'| ≤ C * Real.exp (-(c * max (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ))) := by
  unfold transplantKernel
  by_cases h : p ∈ plaquettesIn (supBall y (R : ℝ)) ∧ p' ∈ plaquettesIn (supBall y (R : ℝ))
  · rw [if_pos h]
    have e1 : _root_.YangMills.Construction.TorusFields.supDist (returnFace y p : TorusPlaquette M).1 (0 : TorusSite M) = _root_.YangMills.Construction.TorusFields.supDist p.1 y := supDist_returnSite hM y (supDist_corner_of_mem h.1)
    have e2 : _root_.YangMills.Construction.TorusFields.supDist (returnFace y p' : TorusPlaquette M).1 (0 : TorusSite M) = _root_.YangMills.Construction.TorusFields.supDist p'.1 y := supDist_returnSite hM y (supDist_corner_of_mem h.2)
    have h1 := hκ (returnFace y p) (returnFace y p')
    have h2 := hκ (returnFace y p') (returnFace y p)
    rw [e1, e2] at h1 h2
    rw [max_comm] at h2
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h3 := abs_add_le (κ (returnFace y p) (returnFace y p')) (κ (returnFace y p') (returnFace y p))
    linarith
  · rw [if_neg h, abs_zero]
    positivity
private theorem lieFormCurl_transplant {R : ℕ} (hM : 2 * (R + 1) < M) (y : TorusSite N) (A : TorusBond N → imaginaryQuaternions) {q : TorusPlaquette M}
    (h : _root_.YangMills.Construction.TorusFields.supDist q.1 0 ≤ R) : lieFormCurl (fun b : TorusBond M => A (transplantSite y b.1, b.2)) q = lieFormCurl A (transplantFace y q) := by
  unfold lieFormCurl
  simp only [transplantFace]
  rw [transplantSite_add_unitStep hM y h q.2.1, transplantSite_add_unitStep hM y h q.2.2]
private theorem curlPairing_comm {n : ℕ} (v : TorusBond n → imaginaryQuaternions) (p p' : TorusPlaquette n) : curlPairing v p p' = curlPairing v p' p := by
  unfold curlPairing
  exact Finset.sum_congr rfl fun e _ => mul_comm _ _
private theorem quadraticForm_transplant {R : ℕ} (hM : 2 * (R + 1) < M) (hN : 2 * (R + 1) < N) (y : TorusSite N) (κ : TorusPlaquette M → TorusPlaquette M → ℝ)
    (A : TorusBond N → imaginaryQuaternions) (S : Finset (TorusPlaquette N)) (hS : plaquettesIn (supBall y (R : ℝ)) ⊆ S) :
    ∑ p ∈ S, ∑ p' ∈ S, transplantKernel y R κ p p' * curlPairing A p p' =
      ∑ q ∈ plaquettesIn (supBall (0 : TorusSite M) (R : ℝ)), ∑ q' ∈ plaquettesIn (supBall (0 : TorusSite M) (R : ℝ)),
        κ q q' * curlPairing (fun b : TorusBond M => A (transplantSite y b.1, b.2)) q q' := by
  set B := plaquettesIn (supBall y (R : ℝ)) with hB
  set B₀ := plaquettesIn (supBall (0 : TorusSite M) (R : ℝ)) with hB₀
  have step1 : ∑ p ∈ S, ∑ p' ∈ S, transplantKernel y R κ p p' * curlPairing A p p' =
      ∑ p ∈ B, ∑ p' ∈ B, transplantKernel y R κ p p' * curlPairing A p p' := by
    rw [← Finset.sum_subset hS]
    · refine Finset.sum_congr rfl fun p hp => ?_
      rw [← Finset.sum_subset hS]
      intro p' _ hp'
      have : transplantKernel y R κ p p' = 0 := by
        unfold transplantKernel
        rw [if_neg fun h => hp' h.2]
      rw [this, zero_mul]
    · intro p _ hp
      refine Finset.sum_eq_zero fun p' _ => ?_
      have : transplantKernel y R κ p p' = 0 := by
        unfold transplantKernel
        rw [if_neg fun h => hp h.1]
      rw [this, zero_mul]
  have hall : ∀ (G : TorusPlaquette N → ℝ), ∑ p ∈ B, G p = ∑ q ∈ B₀, G (transplantFace y q) := by
    intro G
    have := sum_filter_transplant (M := M) hM hN y (fun _ => True) G
    simpa [hB, hB₀] using this
  rw [step1, hall]
  have hin : ∀ q ∈ B₀, transplantFace y q ∈ B := fun q hq => transplantFace_mem hM (by omega) y hq
  have step2 : ∑ q ∈ B₀, ∑ p' ∈ B, transplantKernel y R κ (transplantFace y q) p' * curlPairing A (transplantFace y q) p' =
      ∑ q ∈ B₀, ∑ q' ∈ B₀, (1 / 2) * (κ q q' + κ q' q) *
        curlPairing (fun b : TorusBond M => A (transplantSite y b.1, b.2)) q q' := by
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [hall]
    refine Finset.sum_congr rfl fun q' hq' => ?_
    unfold transplantKernel
    rw [if_pos ⟨hin q hq, hin q' hq'⟩, returnFace_transplantFace (by omega) y hq, returnFace_transplantFace (by omega) y hq']
    congr 1
    unfold curlPairing
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [lieFormCurl_transplant hM y A (supDist_corner_of_mem hq), lieFormCurl_transplant hM y A (supDist_corner_of_mem hq')]
  rw [step2]
  have hswap : ∑ q ∈ B₀, ∑ q' ∈ B₀, κ q' q * curlPairing (fun b : TorusBond M => A (transplantSite y b.1, b.2)) q q' =
      ∑ q ∈ B₀, ∑ q' ∈ B₀, κ q q' * curlPairing (fun b : TorusBond M => A (transplantSite y b.1, b.2)) q q' := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_
    rw [curlPairing_comm]
  have hsplit : ∑ q ∈ B₀, ∑ q' ∈ B₀, (1 / 2) * (κ q q' + κ q' q) *
        curlPairing (fun b : TorusBond M => A (transplantSite y b.1, b.2)) q q' =
      (1 / 2) * (∑ q ∈ B₀, ∑ q' ∈ B₀, κ q q' * curlPairing (fun b : TorusBond M => A (transplantSite y b.1, b.2)) q q') +
      (1 / 2) * (∑ q ∈ B₀, ∑ q' ∈ B₀, κ q' q * curlPairing (fun b : TorusBond M => A (transplantSite y b.1, b.2)) q q') := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q' _ => ?_
    ring
  rw [hsplit, hswap]
  ring
end Transplant
section Truncation
variable {m : ℕ}
private theorem orientedPlaquette_nonempty (m : ℕ) [NeZero m] : Nonempty (OrientedPlaquette m) :=
  ⟨⟨(0, (0, 1)), show (0 : Fin 4) < 1 by decide⟩⟩
private def truncate (B a : ℝ) : ℝ := max (-B) (min B a)
private theorem abs_truncate_sub_le (B a b : ℝ) : |truncate B a - truncate B b| ≤ |a - b| := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.abs_clamp_sub_le <;> assumption
private theorem abs_truncate_le {B : ℝ} (hB : 0 ≤ B) (a : ℝ) : |truncate B a| ≤ B := by apply _root_.YangMills.Construction.ResponseInTheExpansion.RemainderBounds.abs_clamp_le <;> assumption
private theorem truncate_of_abs_le {B a : ℝ} (h : |a| ≤ B) : truncate B a = a := by apply _root_.YangMills.DeltaSharedProofs.p15858 <;> assumption
private theorem abs_le_weightSup [NeZero m] (h : PlaquetteWeight m) (p : OrientedPlaquette m) : |h p.1| ≤ weightSup h :=
  le_ciSup (f := fun p : OrientedPlaquette m => |h p.1|) (Set.finite_range _).bddAbove p
private theorem quotient_le_weightLipschitz [NeZero m] (L t : ℕ) (h : PlaquetteWeight m) (p p' : OrientedPlaquette m) :
    |h p.1 - h p'.1| / barycentreDist L t p.1 p'.1 ≤ weightLipschitz L t h :=
  le_ciSup (f := fun pp : OrientedPlaquette m × OrientedPlaquette m => |h pp.1.1 - h pp.2.1| / barycentreDist L t pp.1.1 pp.2.1)
    (Set.finite_range _).bddAbove (p, p')
private theorem barycentreDist_nonneg' (L t : ℕ) (p p' : TorusPlaquette m) : 0 ≤ barycentreDist L t p p' := by
  unfold barycentreDist
  positivity
private theorem weightLipschitz_nonneg [NeZero m] (L t : ℕ) (h : PlaquetteWeight m) : 0 ≤ weightLipschitz L t h := by
  obtain ⟨p⟩ := orientedPlaquette_nonempty m
  refine le_trans ?_ (quotient_le_weightLipschitz L t h p p)
  have := barycentreDist_nonneg' L t p.1 p.1
  positivity
private theorem weightLipschitz_mono [NeZero m] (L t : ℕ) (h g : PlaquetteWeight m) (H : ∀ p p', |g p - g p'| ≤ |h p - h p'|) :
    weightLipschitz L t g ≤ weightLipschitz L t h := by
  haveI := orientedPlaquette_nonempty m
  unfold weightLipschitz
  refine ciSup_le fun pp => ?_
  refine le_trans ?_ (quotient_le_weightLipschitz L t h pp.1 pp.2)
  exact div_le_div_of_nonneg_right (H _ _) (barycentreDist_nonneg' L t _ _)
private theorem exists_extension_to_torus (L : ℕ) [NeZero L] (hL : Odd L) (hE : weightExtensionStatement)
    (hN : WeightsCloseToBlockMeans) (k N M : ℕ) [NeZero N] [NeZero M] (h4N : 8 ≤ N) (h4M : 8 ≤ M) (y : TorusSite N) (y' : TorusSite M)
    (h : PlaquetteWeight (fineSide L k N)) (hs : weightSup h ≤ 1) :
    ∃ h' : PlaquetteWeight (fineSide L k M), WeightsAgreeAt L k y y' h h' ∧ weightSup h' ≤ 1 ∧ weightLipschitz L k h' ≤ 3 * weightLipschitz L k h := by
  haveI := orientedPlaquette_nonempty (fineSide L k N)
  haveI := orientedPlaquette_nonempty (fineSide L k M)
  set a := blockMean L k N y h with ha
  set B := 3 * weightLipschitz L k h with hB
  have hB0 : 0 ≤ B := by
    have := weightLipschitz_nonneg L k h
    positivity
  set g : PlaquetteWeight (fineSide L k N) := fun p => truncate B (h p - a) with hg
  have hgs : weightSup g ≤ B := ciSup_le fun p => abs_truncate_le hB0 _
  have hgl : weightLipschitz L k g ≤ weightLipschitz L k h := weightLipschitz_mono L k h g fun p p' => by
    refine (abs_truncate_sub_le B _ _).trans (le_of_eq ?_)
    congr 1
    ring
  have hsize : weightNorm L k g ≤ B := by
    unfold weightNorm
    refine max_le hgs (hgl.trans ?_)
    have := weightLipschitz_nonneg L k h
    linarith
  obtain ⟨g', hag, hsg⟩ := hE L hL k N M h4N h4M y y' g
  have hg's : weightLipschitz L k g' ≤ B := (le_max_right _ _).trans (hsg.trans hsize)
  refine ⟨fun q => truncate 1 (a + g' q), ?_, ?_, ?_⟩
  · intro z μ ν hzb hat
    have hat' := hat
    have hnear := (hN L hL k N y).2.1 h _ hat
    have h1 : g (fineCentre L k y + siteOfInt z, μ, ν) = h (fineCentre L k y + siteOfInt z, μ, ν) - a := truncate_of_abs_le hnear
    have h2 := hag z μ ν hzb hat
    have h3 : |h (fineCentre L k y + siteOfInt z, μ, ν)| ≤ 1 :=
      (abs_le_weightSup h ⟨_, hat'.1⟩).trans hs
    show h (fineCentre L k y + siteOfInt z, μ, ν) = truncate 1 (a + g' (fineCentre L k y' + siteOfInt z, μ, ν))
    rw [← h2, h1, show a + (h (fineCentre L k y + siteOfInt z, μ, ν) - a) = h (fineCentre L k y + siteOfInt z, μ, ν) by ring]
    exact (truncate_of_abs_le h3).symm
  · exact ciSup_le fun p => abs_truncate_le zero_le_one _
  · refine le_trans (weightLipschitz_mono L k g' _ fun p p' => ?_) hg's
    refine (abs_truncate_sub_le 1 _ _).trans (le_of_eq ?_)
    congr 1
    ring
end Truncation
private instance neZeroFourMulSucc (R : ℕ) : NeZero (4 * (R + 1)) := ⟨by omega⟩
section MirrorTorus
variable {ℓ : StepParameters}
private def HasCurvedFieldResponse (ℓ : StepParameters) (Kr : ResponseParameters) (C c x₀ : ℝ) : Prop :=
  ∀ (β : ℝ) (k : ℕ) (al : ℕ → ℝ) (n : ℕ) [NeZero n],
      (∀ j ≤ k, ℓ.y₁ ≤ flowCouplings ℓ β j) → x₀ ≤ flowCouplings ℓ β k →
      IsChainResponseCoeff ℓ Kr β k al → |al k| ≤ 2 → ℓ.n₀ ≤ n →
      ∀ (z : TorusSite n) (h : PlaquetteWeight (fineSide ℓ.side k n)), weightSup h ≤ 1 → weightLipschitz ℓ.side k h ≤ 1 →
      ∃ κ : TorusPlaquette n → TorusPlaquette n → ℝ,
        (∀ p p', κ p p' = κ p' p) ∧
        (∀ p p', |κ p p'| ≤ C * Real.exp (-(c * max (_root_.YangMills.Construction.TorusFields.supDist p.1 z : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 z : ℝ)))) ∧
        (∀ μ ν ρ τ : Fin 4, μ < ν → ρ < τ →
          |∑ p ∈ (plaquettesIn Finset.univ).filter (fun p : TorusPlaquette n => p.2 = (μ, ν)),
              ∑ p' ∈ (plaquettesIn Finset.univ).filter (fun p' : TorusPlaquette n => p'.2 = (ρ, τ)), κ p p' -
            (if (μ, ν) = (ρ, τ) then al k * blockMean ℓ.side k n z h else 0)| ≤
              C * (weightLipschitz ℓ.side k h + Real.exp (-(c * n)))) ∧
        ∀ (W : TorusField n) (g : TorusSite n → UnitQuaternion) (v : TorusBond n → imaginaryQuaternions) (ρ s t : ℝ), IsCold ℓ.threshold W →
          1 ≤ ρ → 4 * ρ + 4 ≤ n → 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
          (∀ b : TorusBond n, b.1 ∈ supBall z ρ → ‖(v b : Quaternion ℝ)‖ ≤ s ∧
            ‖(v b : Quaternion ℝ) - (minimalLog (ResponseInTheExpansion.gaugeTransform g W b) : Quaternion ℝ)‖ ≤ s ^ 2) →
          (∀ x ∈ supBall z ρ, ∀ μ ν : Fin 4, curvature W x μ ν ≤ t) →
          (∀ p ∈ plaquettesIn (supBall z ρ), ‖(lieFormCurl v p : Quaternion ℝ)‖ ≤ t) →
            |centeredResponse (coldResponseChain ℓ β (flowCouplings ℓ β) al k) n z W h -
                (1 / 2) * ∑ p ∈ plaquettesIn (supBall z ρ), ∑ p' ∈ plaquettesIn (supBall z ρ),
                  κ p p' * curlPairing v p p'| ≤
              C * (t ^ 3 + t * s ^ 2 + Real.exp (-(c * ρ)))
private theorem curvature_diag {n : ℕ} (W : TorusField n) (x : TorusSite n) (μ : Fin 4) : curvature W x μ μ = 0 := by
  unfold curvature holonomy
  simp
private theorem curvature_mirrorField_le {N m : ℕ} [NeZero N] [NeZero (4 * m)] (hm : 0 < m) (y : TorusSite N) (W : TorusField N) {t : ℝ} (ht : 0 ≤ t)
    (H : ∀ (a : Fin 4 → ℤ) (μ ν : Fin 4), μ ≠ ν → (∀ d ∈ plaquetteOffsets μ ν, OffsetInBox m (a + d)) → curvature W (y + siteOfInt a) μ ν ≤ t)
    (z : TorusSite (4 * m)) (μ ν : Fin 4) : curvature (mirrorField m y W) z μ ν ≤ t := by
  by_cases hne : μ = ν
  · subst hne
    rw [curvature_diag]
    exact ht
  obtain ⟨a, ha, he⟩ := exists_plaquetteEnergy_mirrorField hm y W z hne
  have h1 := H a μ ν hne ha
  rw [plaquetteEnergy_eq_curvature_sq, plaquetteEnergy_eq_curvature_sq] at he
  have h2 : curvature (mirrorField m y W) z μ ν ^ 2 = curvature W (y + siteOfInt a) μ ν ^ 2 := by linarith
  have h3 := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  rw [show curvature (mirrorField m y W) z μ ν = curvature W (y + siteOfInt a) μ ν from h3]
  exact h1
private theorem siteOfInt_valMinAbs {n : ℕ} [NeZero n] (z : TorusSite n) : (siteOfInt (fun i => (z i).valMinAbs) : TorusSite n) = z := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.siteOfInt_minimalCoords <;> assumption
private theorem mirrorField_apply_of_near {N R : ℕ} [NeZero N] (hR : 1 ≤ R) (y : TorusSite N) (W : TorusField N) {z : TorusSite (4 * (R + 1))}
    (hz : _root_.YangMills.Construction.TorusFields.supDist z 0 ≤ R) (i : Fin 4) : mirrorField (R + 1) y W z i = W (transplantSite y z) i := by
  have hb : BondOffsetInBox (R + 1) ((fun j => (z j).valMinAbs), i) := by
    constructor
    · intro j
      have := abs_valMinAbs_le_of_supDist hz j
      push_cast
      omega
    · intro j
      have h1 := abs_le.mp (abs_valMinAbs_le_of_supDist hz j)
      have h2 : ((Pi.single i 1 : Fin 4 → ℤ) j) = 0 ∨ ((Pi.single i 1 : Fin 4 → ℤ) j) = 1 := by
        by_cases hj : j = i
        · subst hj
          simp
        · simp [hj]
      show |(z j).valMinAbs + (Pi.single i 1 : Fin 4 → ℤ) j| ≤ ((R + 1 : ℕ) : ℤ)
      rw [abs_le]
      push_cast
      rcases h2 with h2 | h2 <;> rw [h2] <;> constructor <;> omega
  have := mirrorField_siteOfInt (by omega : 2 ≤ R + 1) y W _ hb
  simp only [siteOfInt_valMinAbs] at this
  exact this
end MirrorTorus
section PlaneSums
variable {N M : ℕ} [NeZero N] [NeZero M]
private theorem supDist_vertex_le_two {m : ℕ} [NeZero m] (x c : TorusSite m) (μ ν : Fin 4) (hc : c ∈ plaquetteVertices x μ ν) : _root_.YangMills.Construction.TorusFields.supDist c x ≤ 2 := by apply _root_.YangMills.SharedProofs.p38261 <;> assumption
private theorem sub_one_le_supDist_of_not_mem {R : ℕ} {q : TorusPlaquette M} (hq : q ∈ plaquettesIn (Finset.univ : Finset (TorusSite M)))
    (hn : q ∉ plaquettesIn (supBall (0 : TorusSite M) (R : ℝ))) : (R : ℝ) - 1 ≤ (_root_.YangMills.Construction.TorusFields.supDist q.1 (0 : TorusSite M) : ℝ) := by
  have h1 := (mem_plaquettesIn'.mp hq).1
  have h2 : ¬ ∀ z ∈ plaquetteVertices q.1 q.2.1 q.2.2, z ∈ supBall (0 : TorusSite M) (R : ℝ) := fun h => hn (mem_plaquettesIn'.mpr ⟨h1, h⟩)
  push_neg at h2
  obtain ⟨z, hz, hz'⟩ := h2
  have h3 : ¬ _root_.YangMills.Construction.TorusFields.supDist z 0 ≤ R := fun h => hz' (mem_supBall_natCast.mpr h)
  have h4 := supDist_vertex_le_two q.1 z _ _ hz
  have h5 := _root_.YangMills.Construction.TorusFields.supDist_triangle z q.1 0
  have h6 : R ≤ _root_.YangMills.Construction.TorusFields.supDist q.1 (0 : TorusSite M) + 1 := by omega
  have : (R : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist q.1 (0 : TorusSite M) : ℝ) + 1 := by exact_mod_cast h6
  linarith
private theorem card_torusPlaquette : Fintype.card (TorusPlaquette M) = M ^ 4 * 16 := by
  simp [TorusPlaquette, TorusSite, Fintype.card_prod, ZMod.card]
private theorem abs_sum_outside_supBall_le (κ : TorusPlaquette M → TorusPlaquette M → ℝ) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (R : ℕ)
    (hκ : ∀ q q', |κ q q'| ≤ C * Real.exp (-(c * max (supDist q.1 (0 : TorusSite M) : ℝ) (supDist q'.1 (0 : TorusSite M) : ℝ))))
    (e₁ e₂ : Fin 4 × Fin 4) :
    |∑ q ∈ (plaquettesIn (Finset.univ : Finset (TorusSite M))).filter (fun q : TorusPlaquette M => q.2 = e₁),
        ∑ q' ∈ (plaquettesIn (Finset.univ : Finset (TorusSite M))).filter (fun q' : TorusPlaquette M => q'.2 = e₂), κ q q' -
      ∑ q ∈ (plaquettesIn (supBall (0 : TorusSite M) (R : ℝ))).filter (fun q : TorusPlaquette M => q.2 = e₁),
        ∑ q' ∈ (plaquettesIn (supBall (0 : TorusSite M) (R : ℝ))).filter (fun q' : TorusPlaquette M => q'.2 = e₂), κ q q'| ≤
      (16 * (M : ℝ) ^ 4) ^ 2 * (C * Real.exp (-(c * ((R : ℝ) - 1)))) := by
  set P₁ := (plaquettesIn (Finset.univ : Finset (TorusSite M))).filter (fun q : TorusPlaquette M => q.2 = e₁) with hP₁
  set P₂ := (plaquettesIn (Finset.univ : Finset (TorusSite M))).filter (fun q : TorusPlaquette M => q.2 = e₂) with hP₂
  set A₁ := (plaquettesIn (supBall (0 : TorusSite M) (R : ℝ))).filter (fun q : TorusPlaquette M => q.2 = e₁) with hA₁
  set A₂ := (plaquettesIn (supBall (0 : TorusSite M) (R : ℝ))).filter (fun q : TorusPlaquette M => q.2 = e₂) with hA₂
  have hsub : ∀ S : Finset (TorusSite M), plaquettesIn S ⊆ plaquettesIn (Finset.univ : Finset (TorusSite M)) := fun S q hq =>
    mem_plaquettesIn'.mpr ⟨(mem_plaquettesIn'.mp hq).1, fun _ _ => Finset.mem_univ _⟩
  have h1 : A₁ ⊆ P₁ := Finset.filter_subset_filter _ (hsub _)
  have h2 : A₂ ⊆ P₂ := Finset.filter_subset_filter _ (hsub _)
  rw [← Finset.sum_product' (f := fun q q' => κ q q'), ← Finset.sum_product' (f := fun q q' => κ q q')]
  have hs := Finset.product_subset_product h1 h2
  rw [← Finset.sum_sdiff hs, add_sub_cancel_right]
  have hb : ∀ x ∈ (P₁ ×ˢ P₂) \ (A₁ ×ˢ A₂), |κ x.1 x.2| ≤ C * Real.exp (-(c * ((R : ℝ) - 1))) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hx1
    have hp1' := Finset.mem_filter.mp hp1
    have hp2' := Finset.mem_filter.mp hp2
    have hfar : (R : ℝ) - 1 ≤ max (_root_.YangMills.Construction.TorusFields.supDist x.1.1 (0 : TorusSite M) : ℝ) (_root_.YangMills.Construction.TorusFields.supDist x.2.1 (0 : TorusSite M) : ℝ) := by
      by_cases hq : x.1 ∈ plaquettesIn (supBall (0 : TorusSite M) (R : ℝ))
      · have hq' : x.2 ∉ plaquettesIn (supBall (0 : TorusSite M) (R : ℝ)) := fun h =>
          hx2 (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hq, hp1'.2⟩, Finset.mem_filter.mpr ⟨h, hp2'.2⟩⟩)
        exact (sub_one_le_supDist_of_not_mem hp2'.1 hq').trans (le_max_right _ _)
      · exact (sub_one_le_supDist_of_not_mem hp1'.1 hq).trans (le_max_left _ _)
    refine (hκ x.1 x.2).trans (mul_le_mul_of_nonneg_left ?_ hC)
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hfar hc.le
    linarith
  have hcardP : ∀ e : Fin 4 × Fin 4, (((plaquettesIn (Finset.univ : Finset (TorusSite M))).filter (fun q : TorusPlaquette M => q.2 = e)).card : ℝ) ≤
      16 * (M : ℝ) ^ 4 := by
    intro e
    have : ((plaquettesIn (Finset.univ : Finset (TorusSite M))).filter (fun q : TorusPlaquette M => q.2 = e)).card ≤ M ^ 4 * 16 := by
      rw [← card_torusPlaquette]
      exact Finset.card_le_univ _
    have h3 : (((plaquettesIn (Finset.univ : Finset (TorusSite M))).filter (fun q : TorusPlaquette M => q.2 = e)).card : ℝ) ≤ ((M ^ 4 * 16 : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at h3
    linarith
  have hcard : ((((P₁ ×ˢ P₂) \ (A₁ ×ˢ A₂)).card : ℕ) : ℝ) ≤ (16 * (M : ℝ) ^ 4) ^ 2 := by
    have h3 : ((P₁ ×ˢ P₂) \ (A₁ ×ˢ A₂)).card ≤ P₁.card * P₂.card := by
      rw [← Finset.card_product]
      exact Finset.card_le_card Finset.sdiff_subset
    have h4 : ((((P₁ ×ˢ P₂) \ (A₁ ×ˢ A₂)).card : ℕ) : ℝ) ≤ (P₁.card : ℝ) * (P₂.card : ℝ) := by exact_mod_cast h3
    refine h4.trans ?_
    rw [sq]
    exact mul_le_mul (hcardP e₁) (hcardP e₂) (by positivity) (by positivity)
  have hnn : 0 ≤ C * Real.exp (-(c * ((R : ℝ) - 1))) := by positivity
  calc |∑ x ∈ (P₁ ×ˢ P₂) \ (A₁ ×ˢ A₂), κ x.1 x.2| ≤ ∑ x ∈ (P₁ ×ˢ P₂) \ (A₁ ×ˢ A₂), |κ x.1 x.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ((((P₁ ×ˢ P₂) \ (A₁ ×ˢ A₂)).card : ℕ) : ℝ) * (C * Real.exp (-(c * ((R : ℝ) - 1)))) := by
        have := Finset.sum_le_card_nsmul _ _ _ hb
        simpa [nsmul_eq_mul] using this
    _ ≤ (16 * (M : ℝ) ^ 4) ^ 2 * (C * Real.exp (-(c * ((R : ℝ) - 1)))) := mul_le_mul_of_nonneg_right hcard hnn
private theorem sum_planes_transplantKernel {R : ℕ} (hM : 2 * (R + 1) < M) (hN : 2 * (R + 1) < N) (y : TorusSite N) (κ : TorusPlaquette M → TorusPlaquette M → ℝ)
    (e₁ e₂ : Fin 4 × Fin 4) :
    ∑ p ∈ (plaquettesIn (Finset.univ : Finset (TorusSite N))).filter (fun p : TorusPlaquette N => p.2 = e₁),
        ∑ p' ∈ (plaquettesIn (Finset.univ : Finset (TorusSite N))).filter (fun p' : TorusPlaquette N => p'.2 = e₂), transplantKernel y R κ p p' =
      (1 / 2) * (∑ q ∈ (plaquettesIn (supBall (0 : TorusSite M) (R : ℝ))).filter (fun q : TorusPlaquette M => q.2 = e₁),
          ∑ q' ∈ (plaquettesIn (supBall (0 : TorusSite M) (R : ℝ))).filter (fun q' : TorusPlaquette M => q'.2 = e₂), κ q q' +
        ∑ q ∈ (plaquettesIn (supBall (0 : TorusSite M) (R : ℝ))).filter (fun q : TorusPlaquette M => q.2 = e₂),
          ∑ q' ∈ (plaquettesIn (supBall (0 : TorusSite M) (R : ℝ))).filter (fun q' : TorusPlaquette M => q'.2 = e₁), κ q q') := by
  set B := plaquettesIn (supBall y (R : ℝ)) with hB
  set B₀ := plaquettesIn (supBall (0 : TorusSite M) (R : ℝ)) with hB₀
  have hsubs : ∀ e : Fin 4 × Fin 4, B.filter (fun p : TorusPlaquette N => p.2 = e) ⊆
      (plaquettesIn (Finset.univ : Finset (TorusSite N))).filter (fun p : TorusPlaquette N => p.2 = e) := fun e =>
    Finset.filter_subset_filter _ fun q hq => mem_plaquettesIn'.mpr ⟨(mem_plaquettesIn'.mp hq).1, fun _ _ => Finset.mem_univ _⟩
  have hoff : ∀ (e : Fin 4 × Fin 4) (p : TorusPlaquette N), p ∈ (plaquettesIn (Finset.univ : Finset (TorusSite N))).filter (fun p : TorusPlaquette N => p.2 = e) →
      p ∉ B.filter (fun p : TorusPlaquette N => p.2 = e) → p ∉ B := fun e p hp hn hb =>
    hn (Finset.mem_filter.mpr ⟨hb, (Finset.mem_filter.mp hp).2⟩)
  have step1 : ∑ p ∈ (plaquettesIn (Finset.univ : Finset (TorusSite N))).filter (fun p : TorusPlaquette N => p.2 = e₁),
        ∑ p' ∈ (plaquettesIn (Finset.univ : Finset (TorusSite N))).filter (fun p' : TorusPlaquette N => p'.2 = e₂), transplantKernel y R κ p p' =
      ∑ p ∈ B.filter (fun p : TorusPlaquette N => p.2 = e₁), ∑ p' ∈ B.filter (fun p' : TorusPlaquette N => p'.2 = e₂), transplantKernel y R κ p p' := by
    rw [← Finset.sum_subset (hsubs e₁)]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Finset.sum_subset (hsubs e₂)]
      intro p' hp' hn
      unfold transplantKernel
      rw [if_neg fun h => hoff e₂ p' hp' hn h.2]
    · intro p hp hn
      refine Finset.sum_eq_zero fun p' _ => ?_
      unfold transplantKernel
      rw [if_neg fun h => hoff e₁ p hp hn h.1]
  have hmv : ∀ (e : Fin 4 × Fin 4) (G : TorusPlaquette N → ℝ), ∑ p ∈ B.filter (fun p : TorusPlaquette N => p.2 = e), G p =
      ∑ q ∈ B₀.filter (fun q : TorusPlaquette M => q.2 = e), G (transplantFace y q) := fun e G =>
    sum_filter_transplant (M := M) hM hN y (fun x => x = e) G
  have hmem : ∀ (e : Fin 4 × Fin 4), ∀ q ∈ B₀.filter (fun q : TorusPlaquette M => q.2 = e), q ∈ B₀ ∧ transplantFace y q ∈ B := fun e q hq =>
    ⟨(Finset.mem_filter.mp hq).1, transplantFace_mem hM (by omega) y (Finset.mem_filter.mp hq).1⟩
  rw [step1, hmv]
  have step2 : ∑ q ∈ B₀.filter (fun q : TorusPlaquette M => q.2 = e₁), ∑ p' ∈ B.filter (fun p' : TorusPlaquette N => p'.2 = e₂),
        transplantKernel y R κ (transplantFace y q) p' =
      ∑ q ∈ B₀.filter (fun q : TorusPlaquette M => q.2 = e₁), ∑ q' ∈ B₀.filter (fun q' : TorusPlaquette M => q'.2 = e₂),
        (1 / 2) * (κ q q' + κ q' q) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [hmv]
    refine Finset.sum_congr rfl fun q' hq' => ?_
    unfold transplantKernel
    rw [if_pos ⟨(hmem e₁ q hq).2, (hmem e₂ q' hq').2⟩, returnFace_transplantFace (by omega) y (hmem e₁ q hq).1,
      returnFace_transplantFace (by omega) y (hmem e₂ q' hq').1]
  rw [step2, Finset.sum_comm (s := B₀.filter (fun q : TorusPlaquette M => q.2 = e₂))]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
end PlaneSums
section SiteKernels
variable {ℓ : StepParameters}
private theorem exists_site_kernel {Kr : ResponseParameters} {C c x₀ : ℝ} (hmark : HasCurvedFieldResponse ℓ Kr C c x₀) (hc : 0 < c)
    (hodd : Odd ℓ.side) (hE : weightExtensionStatement) (hN : WeightsCloseToBlockMeans)
    (hT : WeightsCompatibleAcrossTori) {β : ℝ} {k : ℕ} {al : ℕ → ℝ}
    (hfl : ∀ j ≤ k, ℓ.y₁ ≤ flowCouplings ℓ β j) (hx : x₀ ≤ flowCouplings ℓ β k) (hnum : IsChainResponseCoeff ℓ Kr β k al) (hal : |al k| ≤ 2)
    {N R : ℕ} [NeZero N] (hR : 2 ≤ R) (hRn : ℓ.n₀ ≤ 4 * (R + 1)) (hNR : 2 * (R + 2) < N) (y : TorusSite N)
    (h : PlaquetteWeight (fineSide ℓ.side k N)) (hs : weightSup h ≤ 1) (hl : 3 * weightLipschitz ℓ.side k h ≤ 1) :
    ∃ (h' : PlaquetteWeight (fineSide ℓ.side k (4 * (R + 1)))) (κ : TorusPlaquette N → TorusPlaquette N → ℝ),
      WeightsAgreeAt ℓ.side k y 0 h h' ∧
      (∀ p p', κ p p' = κ p' p) ∧
      (∀ p p', |κ p p'| ≤ C * Real.exp (-(c * max (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ)))) ∧
      (∀ μ ν ρ τ : Fin 4, μ < ν → ρ < τ →
        |∑ p ∈ (plaquettesIn Finset.univ).filter (fun p : TorusPlaquette N => p.2 = (μ, ν)),
            ∑ p' ∈ (plaquettesIn Finset.univ).filter (fun p' : TorusPlaquette N => p'.2 = (ρ, τ)), κ p p' -
          (if (μ, ν) = (ρ, τ) then al k * blockMean ℓ.side k N y h else 0)| ≤
            C * (3 * weightLipschitz ℓ.side k h + Real.exp (-(c * ((4 * (R + 1) : ℕ) : ℝ)))) +
              (16 * (((4 * (R + 1) : ℕ) : ℝ)) ^ 4) ^ 2 * (C * Real.exp (-(c * ((R : ℝ) - 1))))) ∧
      ∀ (W : TorusField N) (G : TorusSite N → UnitQuaternion) (A : TorusBond N → imaginaryQuaternions) (s t : ℝ), 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → t < ℓ.threshold →
        (∀ (a : Fin 4 → ℤ) (μ ν : Fin 4), μ ≠ ν → (∀ d ∈ plaquetteOffsets μ ν, OffsetInBox (R + 1) (a + d)) →
          curvature W (y + siteOfInt a) μ ν ≤ t) →
        (∀ b : TorusBond N, _root_.YangMills.Construction.TorusFields.supDist b.1 y ≤ R → ‖(A b : Quaternion ℝ)‖ ≤ s ∧
          ‖(A b : Quaternion ℝ) - (minimalLog (TorusFields.gaugeTransform G W b.1 b.2) : Quaternion ℝ)‖ ≤ s ^ 2) →
        (∀ p ∈ plaquettesIn (supBall y (R : ℝ)), ‖(lieFormCurl A p : Quaternion ℝ)‖ ≤ t) →
        ∀ S : Finset (TorusPlaquette N), plaquettesIn (supBall y (R : ℝ)) ⊆ S →
          |centeredResponse (coldResponseChain ℓ β (flowCouplings ℓ β) al k) (4 * (R + 1)) 0 (mirrorField (R + 1) y W) h' -
              (1 / 2) * ∑ p ∈ S, ∑ p' ∈ S, κ p p' * curlPairing A p p'| ≤
            C * (t ^ 3 + t * s ^ 2 + Real.exp (-(c * (R : ℝ)))) := by
  have h4N : 8 ≤ N := by omega
  have h4M : 8 ≤ 4 * (R + 1) := by omega
  have hM1 : 2 * (R + 1) < 4 * (R + 1) := by omega
  have hN1 : 2 * (R + 1) < N := by omega
  obtain ⟨h', hag, hs', hl'⟩ := exists_extension_to_torus ℓ.side hodd hE hN k N (4 * (R + 1)) h4N h4M y 0 h hs
  have hl1 : weightLipschitz ℓ.side k h' ≤ 1 := hl'.trans hl
  obtain ⟨κ', -, hd, hp, hf⟩ := hmark β k al (4 * (R + 1)) hfl hx hnum hal hRn 0 h' hs' hl1
  have hC0 : 0 ≤ C := by
    have h1 := (abs_nonneg _).trans (hd (0, (0, 0)) (0, (0, 0)))
    exact nonneg_of_mul_nonneg_left h1 (Real.exp_pos _)
  refine ⟨h', transplantKernel y R κ', hag, transplantKernel_symm y R κ', abs_transplantKernel_le (by omega) y κ' hC0 hd, ?_, ?_⟩
  · intro μ ν ρ τ hμ hρ
    have hps := sum_planes_transplantKernel (M := 4 * (R + 1)) hM1 hN1 y κ' (μ, ν) (ρ, τ)
    rw [hps]
    have t₁ := abs_sum_outside_supBall_le κ' hC0 hc R hd (μ, ν) (ρ, τ)
    have t₂ := abs_sum_outside_supBall_le κ' hC0 hc R hd (ρ, τ) (μ, ν)
    have p₁ := hp μ ν ρ τ hμ hρ
    have p₂ := hp ρ τ μ ν hρ hμ
    have hhat : blockMean ℓ.side k (4 * (R + 1)) 0 h' = blockMean ℓ.side k N y h := ((hT ℓ.side hodd k N (4 * (R + 1))).2.1 y 0 h h' hag).symm
    rw [hhat] at p₁ p₂
    have hif : (if ((ρ, τ) : Fin 4 × Fin 4) = (μ, ν) then al k * blockMean ℓ.side k N y h else 0) =
        (if ((μ, ν) : Fin 4 × Fin 4) = (ρ, τ) then al k * blockMean ℓ.side k N y h else 0) := by
      by_cases he : ((μ, ν) : Fin 4 × Fin 4) = (ρ, τ)
      · rw [if_pos he, if_pos he.symm]
      · rw [if_neg he, if_neg fun e => he e.symm]
    rw [hif] at p₂
    have hE1 : C * (weightLipschitz ℓ.side k h' + Real.exp (-(c * ((4 * (R + 1) : ℕ) : ℝ)))) ≤
        C * (3 * weightLipschitz ℓ.side k h + Real.exp (-(c * ((4 * (R + 1) : ℕ) : ℝ)))) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    obtain ⟨a1, a2⟩ := abs_le.mp (t₁)
    obtain ⟨b1, b2⟩ := abs_le.mp (t₂)
    obtain ⟨c1, c2⟩ := abs_le.mp (p₁)
    obtain ⟨d1, d2⟩ := abs_le.mp (p₂)
    rw [abs_le]
    constructor <;> linarith
  · intro W G A s t hs0 hs1 ht0 ht1 hts H3 H2 H4 S hS
    have hcurv := curvature_mirrorField_le (m := R + 1) (by omega) y W ht0 H3
    have hcold : IsCold ℓ.threshold (mirrorField (R + 1) y W) := fun z μ ν _ => (hcurv z μ ν).trans_lt hts
    have hform := hf (mirrorField (R + 1) y W) (fun z => G (transplantSite y z)) (fun b => A (transplantSite y b.1, b.2)) (R : ℝ) s t hcold
      (by exact_mod_cast (show 1 ≤ R by omega)) (by push_cast; linarith) hs0 hs1 ht0 ht1 ?_ (fun x _ μ ν => hcurv x μ ν) ?_
    · rw [quadraticForm_transplant hM1 hN1 y κ' A S hS]
      exact hform
    · intro b hb
      have hz : _root_.YangMills.Construction.TorusFields.supDist b.1 0 ≤ R := mem_supBall_natCast.mp hb
      have hτ : _root_.YangMills.Construction.TorusFields.supDist (transplantSite y b.1) y ≤ R := by
        rw [supDist_transplantSite (r := R) (by omega) y hz]
        exact hz
      obtain ⟨h1, h2⟩ := H2 (transplantSite y b.1, b.2) hτ
      have hg : ResponseInTheExpansion.gaugeTransform (fun z => G (transplantSite y z)) (mirrorField (R + 1) y W) b = TorusFields.gaugeTransform G W (transplantSite y b.1) b.2 := by
        unfold ResponseInTheExpansion.gaugeTransform TorusFields.gaugeTransform
        simp only
        rw [mirrorField_apply_of_near (by omega) y W hz, transplantSite_add_unitStep (r := R) (by omega) y hz b.2]
      rw [hg]
      exact ⟨h1, h2⟩
    · intro p hp'
      rw [lieFormCurl_transplant hM1 y A (supDist_corner_of_mem hp')]
      exact H4 _ (transplantFace_mem hM1 (by omega) y hp')
end SiteKernels
section Estimates
private theorem le_rpow_of_rpow_inv_le {a A x : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (h : A ^ (1 / a) ≤ x) : A ≤ x ^ a := by
  have h1 : (A ^ (1 / a)) ^ a ≤ x ^ a := Real.rpow_le_rpow (Real.rpow_nonneg hA _) h ha.le
  rw [← Real.rpow_mul hA, one_div, inv_mul_cancel₀ ha.ne', Real.rpow_one] at h1
  exact h1
private theorem boxRadius_bounds {x : ℝ} (hx : 1 ≤ x) :
    x ^ ((1 : ℝ) / 27) ≤ (boxRadius x : ℝ) ∧ (boxRadius x : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 27) := by
  have h1 : 1 ≤ x ^ ((1 : ℝ) / 27) := Real.one_le_rpow hx (by norm_num)
  unfold boxRadius
  refine ⟨Nat.le_ceil _, ?_⟩
  have := Nat.ceil_lt_add_one (show 0 ≤ x ^ ((1 : ℝ) / 27) by linarith)
  linarith
abbrev _root_.YangMills.SharedProofs.p14121 := @boxRadius_bounds
private theorem log_le_rpow_div' {x : ℝ} (hx : 0 ≤ x) (a : ℝ) (ha : 0 < a) : Real.log x ≤ x ^ a / a := Real.log_le_rpow_div hx ha
private theorem boxScale_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ boxScale x := by apply _root_.YangMills.SharedProofs.p57587 <;> assumption
private theorem boxRadius_cube_mul_boxScale_le {x : ℝ} (hx : 1 ≤ x) :
    (boxRadius x : ℝ) ^ 3 * boxScale x ≤ 160 * x ^ (-(26 / 90 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨-, h2⟩ := boxRadius_bounds hx
  have h3 : (boxRadius x : ℝ) ^ 3 ≤ (2 * x ^ ((1 : ℝ) / 27)) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) h2 3
  have h4 : Real.log x ≤ x ^ ((1 : ℝ) / 10) / (1 / 10) := log_le_rpow_div' hx0.le _ (by norm_num)
  have h5 : boxScale x ≤ 2 * x ^ (-(1 / 2 : ℝ)) * (x ^ ((1 : ℝ) / 10) / (1 / 10)) := by
    unfold boxScale
    exact mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : (2 * x ^ ((1 : ℝ) / 27)) ^ 3 * (2 * x ^ (-(1 / 2 : ℝ)) * (x ^ ((1 : ℝ) / 10) / (1 / 10))) =
      160 * x ^ (-(26 / 90 : ℝ)) := by
    have e : x ^ (-(26 / 90 : ℝ)) = (x ^ ((1 : ℝ) / 27)) ^ 3 * (x ^ (-(1 / 2 : ℝ)) * x ^ ((1 : ℝ) / 10)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
      norm_num
    rw [e]
    ring
  calc (boxRadius x : ℝ) ^ 3 * boxScale x ≤ (2 * x ^ ((1 : ℝ) / 27)) ^ 3 *
        (2 * x ^ (-(1 / 2 : ℝ)) * (x ^ ((1 : ℝ) / 10) / (1 / 10))) :=
        mul_le_mul h3 h5 (boxScale_nonneg hx) (by positivity)
    _ = 160 * x ^ (-(26 / 90 : ℝ)) := h6
private theorem mul_boxRadius_cube_boxScale_le_one {D x : ℝ} (hD : 0 ≤ D) (hx : 1 ≤ x) (hf : (160 * D) ^ (1 / (26 / 90 : ℝ)) ≤ x) :
    D * ((boxRadius x : ℝ) ^ 3 * boxScale x) ≤ 1 := by
  have hx0 : 0 < x := by linarith
  have h1 : 160 * D ≤ x ^ (26 / 90 : ℝ) := le_rpow_of_rpow_inv_le (by norm_num) (by positivity) hf
  have h2 := boxRadius_cube_mul_boxScale_le hx
  have h3 : x ^ (-(26 / 90 : ℝ)) * x ^ (26 / 90 : ℝ) = 1 := by
    rw [← Real.rpow_add hx0]
    norm_num
  have h4 : 0 < x ^ (-(26 / 90 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  calc D * ((boxRadius x : ℝ) ^ 3 * boxScale x) ≤ D * (160 * x ^ (-(26 / 90 : ℝ))) :=
        mul_le_mul_of_nonneg_left h2 hD
    _ = (160 * D) * x ^ (-(26 / 90 : ℝ)) := by ring
    _ ≤ x ^ (26 / 90 : ℝ) * x ^ (-(26 / 90 : ℝ)) := mul_le_mul_of_nonneg_right h1 h4.le
    _ = 1 := by rw [mul_comm, h3]
private theorem exp_neg_boxRadius_le {c x : ℝ} (hc : 0 < c) (hx : Real.exp 1 ≤ x) (hf : (81 / c) ^ (1 / (1 / 54 : ℝ)) ≤ x) :
    Real.exp (-(c * (boxRadius x : ℝ))) ≤ (boxRadius x : ℝ) ^ 8 * boxScale x ^ 3 := by
  have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num)).trans hx
  have hx0 : 0 < x := by linarith
  obtain ⟨h1, -⟩ := boxRadius_bounds hx1
  have hlog : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) hx
  have hw : 81 / c ≤ x ^ (1 / 54 : ℝ) := le_rpow_of_rpow_inv_le (by norm_num) (by positivity) hf
  set w := x ^ (1 / 54 : ℝ) with hwdef
  have hw0 : 0 < w := Real.rpow_pos_of_pos hx0 _
  have hww : x ^ ((1 : ℝ) / 27) = w * w := by
    rw [hwdef, ← Real.rpow_add hx0]
    norm_num
  have h2 : Real.log x ≤ 54 * w := by
    have := log_le_rpow_div' hx0.le (1 / 54 : ℝ) (by norm_num)
    rw [← hwdef] at this
    linarith
  have h3 : (3 / 2) * Real.log x ≤ c * (boxRadius x : ℝ) := by
    have e1 : 81 ≤ c * w := by
      rw [div_le_iff₀ hc] at hw
      linarith
    calc (3 / 2) * Real.log x ≤ 81 * w := by linarith
      _ ≤ (c * w) * w := mul_le_mul_of_nonneg_right e1 hw0.le
      _ = c * x ^ ((1 : ℝ) / 27) := by rw [hww]; ring
      _ ≤ c * (boxRadius x : ℝ) := mul_le_mul_of_nonneg_left h1 hc.le
  have h4 : Real.exp (-(c * (boxRadius x : ℝ))) ≤ x ^ (-(3 / 2 : ℝ)) := by
    rw [Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    linarith
  have h5 : x ^ (-(1 / 2 : ℝ)) ≤ boxScale x := by
    unfold boxScale
    have h6 : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
    nlinarith
  have h7 : x ^ (-(3 / 2 : ℝ)) = (x ^ (-(1 / 2 : ℝ))) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have h8 : (x ^ (-(1 / 2 : ℝ))) ^ 3 ≤ boxScale x ^ 3 :=
    pow_le_pow_left₀ (Real.rpow_nonneg hx0.le _) h5 3
  have h9 : 1 ≤ (boxRadius x : ℝ) ^ 8 := one_le_pow₀ ((Real.one_le_rpow hx1 (by norm_num)).trans h1)
  have h10 : 0 ≤ boxScale x ^ 3 := pow_nonneg (boxScale_nonneg hx1) 3
  calc Real.exp (-(c * (boxRadius x : ℝ))) ≤ boxScale x ^ 3 := h4.trans (h7 ▸ h8)
    _ ≤ (boxRadius x : ℝ) ^ 8 * boxScale x ^ 3 := le_mul_of_one_le_left h10 h9
private theorem pow_eight_le_exp {c : ℝ} (hc : 0 < c) (R : ℝ) (hR : 0 ≤ R) :
    R ^ 8 ≤ (Nat.factorial 8 : ℝ) * (2 / c) ^ 8 * Real.exp (c / 2 * R) := by
  have h1 := Real.pow_div_factorial_le_exp (c / 2 * R) (by positivity) 8
  have hf : (0 : ℝ) < (Nat.factorial 8 : ℝ) := by positivity
  rw [div_le_iff₀ hf] at h1
  have h2 : R ^ 8 = (2 / c) ^ 8 * (c / 2 * R) ^ 8 := by
    field_simp
  rw [h2]
  have h3 : 0 ≤ (2 / c) ^ 8 := by positivity
  calc (2 / c) ^ 8 * (c / 2 * R) ^ 8 ≤ (2 / c) ^ 8 * (Real.exp (c / 2 * R) * (Nat.factorial 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 h3
    _ = (Nat.factorial 8 : ℝ) * (2 / c) ^ 8 * Real.exp (c / 2 * R) := by ring
end Estimates
section CouplingFlow
private theorem expansion_succ_of_returns {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ} {D : TorusFunctional}
    (hx : ℓ.y₁ ≤ x) (hD : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
private theorem hasExpansion_couplingFlow {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {β : ℝ}
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) (t : ℕ) :
    (∀ j < t, ℓ.y₁ ≤ flowCouplings ℓ β j) → HasExpansion ℓ t (couplingFlow ℓ β t).1 (couplingFlow ℓ β t).2 := by apply _root_.YangMills.DeltaSharedProofs.p3925 <;> assumption
abbrev _root_.YangMills.SharedProofs.p48744 := @hasExpansion_couplingFlow
private theorem abs_flowCouplings_succ_sub_le {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {β : ℝ}
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) {K : ℕ} (hfl : ∀ j ≤ K, ℓ.y₁ ≤ flowCouplings ℓ β j)
    {t : ℕ} (ht : t < K) : |flowCouplings ℓ β (t + 1) - flowCouplings ℓ β t| ≤ 2 * ℓ.B :=
  (expansion_succ_of_returns hR (hfl t ht.le)
    (hasExpansion_couplingFlow hR h0 t fun j hj => hfl j (hj.trans ht).le)).2
private theorem boxRadius_add_three_le_pow {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {β Xi : ℝ} (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) {K k : ℕ}
    (hfl : ∀ j ≤ K, ℓ.y₁ ≤ flowCouplings ℓ β j) (htop : flowCouplings ℓ β K ≤ Xi) (hk : k < K) (hL : 2 ≤ ℓ.side)
    {x : ℝ} (hx : x = flowCouplings ℓ β k) (hx1 : 1 ≤ x)
    (hf : (|Xi| + 8 * |ℓ.B| + 1) ^ (1 / (26 / 27 : ℝ)) ≤ x) :
    boxRadius x + 3 ≤ ℓ.side ^ (K - k - 1) := by
  have hx0 : 0 < x := by linarith
  have hB : 0 ≤ 2 * ℓ.B := (abs_nonneg _).trans (abs_flowCouplings_succ_sub_le hR h0 hfl hk)
  have hdesc : ∀ i : ℕ, k + i ≤ K → flowCouplings ℓ β k ≤ flowCouplings ℓ β (k + i) + 2 * ℓ.B * i := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := abs_le.mp (abs_flowCouplings_succ_sub_le hR h0 hfl (show k + i < K by omega))
      rw [show k + (i + 1) = k + i + 1 by ring]
      push_cast
      linarith [h2.1]
  set J := K - k with hJ
  have h1 := hdesc J (by omega)
  rw [show k + J = K by omega, ← hx] at h1
  by_contra hcon
  push_neg at hcon
  have hJ1 : 1 ≤ J := by omega
  have hJ2 : J ≤ ℓ.side ^ (J - 1) := by
    have e1 : J - 1 < 2 ^ (J - 1) := Nat.lt_two_pow_self
    have e2 : 2 ^ (J - 1) ≤ ℓ.side ^ (J - 1) := Nat.pow_le_pow_left hL _
    omega
  have hJ3 : (J : ℝ) ≤ (boxRadius x : ℝ) + 2 := by
    have : J ≤ boxRadius x + 2 := by omega
    exact_mod_cast this
  obtain ⟨-, hr⟩ := boxRadius_bounds hx1
  set q := x ^ ((1 : ℝ) / 27) with hq
  have hq1 : 1 ≤ q := Real.one_le_rpow hx1 (by norm_num)
  have hJ4 : (J : ℝ) ≤ 4 * q := by linarith
  have hXq : Xi ≤ |Xi| * q := by
    have := le_abs_self Xi
    have h3 : |Xi| ≤ |Xi| * q := le_mul_of_one_le_right (abs_nonneg _) hq1
    linarith
  have hBabs : ℓ.B ≤ |ℓ.B| := le_abs_self _
  have h2 : x ≤ (|Xi| + 8 * |ℓ.B|) * q := by
    have e1 : 2 * ℓ.B * (J : ℝ) ≤ 2 * ℓ.B * (4 * q) := mul_le_mul_of_nonneg_left hJ4 hB
    have e2 : ℓ.B * q ≤ |ℓ.B| * q := mul_le_mul_of_nonneg_right hBabs (by linarith)
    nlinarith
  have h3 : |Xi| + 8 * |ℓ.B| + 1 ≤ x ^ (26 / 27 : ℝ) :=
    le_rpow_of_rpow_inv_le (by norm_num) (by positivity) hf
  have h4 : x = q * x ^ (26 / 27 : ℝ) := by
    rw [hq, ← Real.rpow_add hx0]
    norm_num
  have h5 : q * (|Xi| + 8 * |ℓ.B| + 1) ≤ x :=
    calc q * (|Xi| + 8 * |ℓ.B| + 1) ≤ q * x ^ (26 / 27 : ℝ) := mul_le_mul_of_nonneg_left h3 (by linarith)
      _ = x := h4.symm
  nlinarith
end CouplingFlow
section Bumps
private structure IsBoundedLipschitzBump (d vt : ℝ) (c : AmbientSpace) (g : AmbientSpace → ℝ) : Prop where
  abs_le_one : ∀ x, |g x| ≤ 1
  abs_sub_le : ∀ x x', |g x - g x'| ≤ TorusMetric.euclidNormVec (x - x') / (vt * d)
  support_subset : ∀ x, g x ≠ 0 → TorusMetric.euclidNormVec (x - c) ≤ d
private theorem isBoundedLipschitzBump_of_shaped {d vt : ℝ} {c : AmbientSpace} {g : AmbientSpace → ℝ} (hd : 0 < d) (hvt : 0 < vt)
    (ht : TestFunctions.IsShapedBump TestFunctions.euclidDistR4 TestFunctions.closedBallR4 (fun f => ∫ x, f x) d vt c g)
    (h1 : TestFunctions.uniformNorm g = 1) : IsBoundedLipschitzBump d vt c g := by
  obtain ⟨hL, -, -, hsup, -, hlip⟩ := ht
  rw [h1] at hlip
  refine ⟨fun x => ?_, fun x x' => ?_, fun x hx => ?_⟩
  · have hb : BddAbove (Set.range fun x => ‖g x‖) := by
      by_contra hb
      have := Real.iSup_of_not_bddAbove hb
      unfold TestFunctions.uniformNorm at h1
      rw [this] at h1
      norm_num at h1
    exact le_trans (le_ciSup hb x) (le_of_eq h1)
  · obtain ⟨C₀, hC₀, hC₀'⟩ := hL
    set S : Set ℝ := {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖g x - g y‖ ≤ C * TestFunctions.euclidDistR4 x y} with hS
    have hne : S.Nonempty := ⟨C₀, hC₀, hC₀'⟩
    have hD : 0 ≤ TestFunctions.euclidDistR4 x x' := Real.sqrt_nonneg _
    have hbound : ‖g x - g x'‖ ≤ sInf S * TestFunctions.euclidDistR4 x x' := by
      rcases hD.eq_or_lt with h0 | h0
      · have := hC₀' x x'
        rw [← h0, mul_zero] at this
        rw [← h0, mul_zero]
        exact this
      · rw [← div_le_iff₀ h0]
        exact le_csInf hne fun C hC => (div_le_iff₀ h0).mpr (hC.2 x x')
    have hl2 : sInf S ≤ 1 / (vt * d) := hlip
    have h3 : sInf S * TestFunctions.euclidDistR4 x x' ≤ 1 / (vt * d) * TestFunctions.euclidDistR4 x x' :=
      mul_le_mul_of_nonneg_right hl2 hD
    have h4 : TestFunctions.euclidDistR4 x x' = TorusMetric.euclidNormVec (x - x') := rfl
    rw [h4] at h3 hbound
    calc |g x - g x'| = ‖g x - g x'‖ := rfl
      _ ≤ TorusMetric.euclidNormVec (x - x') / (vt * d) := by
        refine hbound.trans (h3.trans (le_of_eq ?_))
        ring
  · have h2 : x ∈ tsupport g := subset_tsupport _ hx
    exact hsup h2
private theorem isBoundedLipschitzBump_translate {d vt : ℝ} {c : AmbientSpace} {g : AmbientSpace → ℝ} (L K k : ℕ) (v : Fin 4 → ℤ)
    (hb : IsBoundedLipschitzBump d vt c g) :
    IsBoundedLipschitzBump d vt (c + latticeShift L K k v) (translateBy L K k v g) := by
  refine ⟨fun x => hb.abs_le_one _, fun x x' => ?_, fun x hx => ?_⟩
  · have := hb.abs_sub_le (x - latticeShift L K k v) (x' - latticeShift L K k v)
    rwa [sub_sub_sub_cancel_right] at this
  · have := hb.support_subset _ hx
    rwa [sub_sub, add_comm (latticeShift L K k v) c] at this
end Bumps
section Assembly
variable {ℓ : StepParameters}
private theorem glueField_restrict {n : ℕ} [NeZero n] (o : TorusSite n) (R : ℕ) (W : TorusField n) : glueField (restrictOuter o R W) (restrictInner o R W) = W := by
  funext x i
  unfold glueField
  split_ifs <;> rfl
private theorem curvature_swap {n : ℕ} (W : TorusField n) (x : TorusSite n) (μ ν : Fin 4) : curvature W x ν μ = curvature W x μ ν := by apply _root_.YangMills.SharedProofs.p108355 <;> assumption
set_option maxHeartbeats 3200000 in
private theorem exists_kernelFamily_of_bump {Kr : ResponseParameters} {Cm cm xm cf : ℝ} (hmark : HasCurvedFieldResponse ℓ Kr Cm cm xm) (hcm : 0 < cm)
    (hodd : Odd ℓ.side) (hE : weightExtensionStatement) (hN : WeightsCloseToBlockMeans)
    (hT : WeightsCompatibleAcrossTori) (hS : unitTorusWeightSizesStatement) (hW : BlockMeanIsLinearAndLocal)
    {d vt : ℝ} (hd0 : 0 < d) (hd : d < 1 / 2) (hvt : 0 < vt) {K k mq R : ℕ} (hkK : k ≤ K) {β x : ℝ} {al : ℕ → ℝ}
    {T : StageTower ℓ} {o : TorusSite (boxSide ℓ.side K k)} (c : BoxChart T k o R) {C₁ c₀ ε φ₀ : ℝ} {Cj xp : ℕ → ℝ}
    (hfl : ∀ j ≤ k, ℓ.y₁ ≤ flowCouplings ℓ β j) (hx : x = flowCouplings ℓ β k) (hxm : xm ≤ x) (hnum : IsChainResponseCoeff ℓ Kr β k al) (hal : |al k| ≤ 2)
    (hF : ∀ h : PlaquetteWeight (fineSide ℓ.side k (boxSide ℓ.side K k)), ∀ᵐ u ∂(markedSampleLaw T β k (boxSide ℓ.side K k)), ∃ F : TorusSite (boxSide ℓ.side K k) → ℝ,
        response T β al k (boxSide ℓ.side K k) h u =
            ∑ z, F z + ∑ z, coldResponseChain ℓ β (flowCouplings ℓ β) al k (boxSide ℓ.side K k) z (trivialField (boxSide ℓ.side K k)) h ∧
        (∀ z, z ∉ weightSupportSites ℓ.side k (boxSide ℓ.side K k) h → F z = 0) ∧
        ∀ (z : TorusSite (boxSide ℓ.side K k)) (n' : ℕ) [NeZero n'] (W' : TorusField n') (z' : TorusSite n') (m : ℕ)
          (ω' : (∅ : Finset (TorusSite n')) → (T.stage k).labels.Ω) (h' : PlaquetteWeight (fineSide ℓ.side k n')),
          ℓ.n₀ ≤ n' → IsCold ℓ.threshold W' →
          (clusterRange (flowCouplings ℓ β k) : ℝ) / 64 ≤ m →
          StatesAgreeNear ℓ (stageState T k (boxSide ℓ.side K k) u).1 W' (stageState T k (boxSide ℓ.side K k) u).2.1 ∅
            (stageState T k (boxSide ℓ.side K k) u).2.2 ω' z z' m →
          WeightsAgreeAt ℓ.side k z z' h h' →
          |F z - centeredResponse (coldResponseChain ℓ β (flowCouplings ℓ β) al k) n' z' W' h'| ≤
            Real.exp (-(cf * m)) * weightNorm ℓ.side k h)
    (hchart : IsGoodChart T β K k c x C₁ c₀ ε φ₀ Cj xp)
    (hR : 16 ≤ R) (hRn : ℓ.n₀ ≤ 4 * (R + 1)) (hNR : 2 * (R + 2) < boxSide ℓ.side K k)
    (hr : (clusterRange x : ℝ) / 64 ≤ R)
    {U t : ℝ} (hU0 : 0 ≤ U) (ht0 : 0 ≤ t) (hU : C₁ * (R : ℝ) ^ 3 * boxScale x ≤ U) (hU1 : 2 * U ≤ 1) (ht : C₁ * (R : ℝ) ^ 2 * boxScale x ≤ t) (ht1 : t ≤ 1)
    (hct : C₁ * (R : ℝ) ^ 4 * boxScale x ^ 2 ≤ t ^ 2) (hts : t < ℓ.threshold) (hlip : 3 * (2 / (vt * lengthInSites ℓ.side K k d)) ≤ 1)
    {Cf cc errK err : ℝ} (hCf : Cm ≤ Cf) (hcc : cc ≤ cm) (hcc0 : 0 ≤ cc)
    (herrK : Cm * (3 * (2 / (vt * lengthInSites ℓ.side K k d)) + Real.exp (-(cm * ((4 * (R + 1) : ℕ) : ℝ)))) +
      (16 * (((4 * (R + 1) : ℕ) : ℝ)) ^ 4) ^ 2 * (Cm * Real.exp (-(cm * ((R : ℝ) - 1)))) ≤ errK)
    (herr : (4 * lengthInSites ℓ.side K k d + 11) ^ 4 *
      (Real.exp (-(cf * (R : ℝ))) + Cm * (t ^ 3 + t * (2 * U) ^ 2 + Real.exp (-(cm * (R : ℝ))))) ≤ err)
    {g : AmbientSpace → ℝ} {cg : AmbientSpace} (hg : IsBoundedLipschitzBump d vt cg g) (hnear : IsLocalizedNear ℓ.side K k mq R o g) :
    ∃ (κ : (Fin 4 → ℤ) → TorusSite (boxSide ℓ.side K k) → TorusPlaquette (boxSide ℓ.side K k) → TorusPlaquette (boxSide ℓ.side K k) → ℝ) (κ₀ : (Fin 4 → ℤ) → ℝ),
      IsBoxKernelFamily T β al K k mq c Cf cc errK err (fun v => translateBy ℓ.side K k v g) κ κ₀ := by
  have hxk : (flowCouplings ℓ β k) = x := hx.symm
  have hR1 : 2 ≤ R := by omega
  have hRr : (16 : ℝ) ≤ R := by exact_mod_cast hR
  have hnpos : 0 < lengthInSites ℓ.side K k d := by
    have hLpos : (0 : ℝ) < ℓ.side := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ.side)
    unfold lengthInSites
    positivity
  have hw : ∀ v : Fin 4 → ℤ, weightSup (unitTorusWeight ℓ.side K k (translateBy ℓ.side K k v g)) ≤ 1 ∧
      weightLipschitz ℓ.side k (unitTorusWeight ℓ.side K k (translateBy ℓ.side K k v g)) ≤ 2 / (vt * lengthInSites ℓ.side K k d) ∧
      ((weightSupportSites ℓ.side k (boxSide ℓ.side K k) (unitTorusWeight ℓ.side K k (translateBy ℓ.side K k v g))).card : ℝ) ≤ (4 * lengthInSites ℓ.side K k d + 11) ^ 4 := fun v => by
    have hb := isBoundedLipschitzBump_translate ℓ.side K k v hg
    exact hS ℓ.side hodd K k hkK d vt _ _ hd0 hd hvt hb.abs_le_one hb.abs_sub_le hb.support_subset
  have hxm' : xm ≤ flowCouplings ℓ β k := hx ▸ hxm
  have hsite := fun (v : Fin 4 → ℤ) (y : TorusSite (boxSide ℓ.side K k)) =>
    exists_site_kernel hmark hcm hodd hE hN hT hfl hxm' hnum hal hR1 hRn hNR y (unitTorusWeight ℓ.side K k (translateBy ℓ.side K k v g)) (hw v).1
      (by linarith [(hw v).2.1])
  choose H κs hag hsym hdec hpl hform using hsite
  have hCm0 : 0 ≤ Cm := by
    have h1 := (abs_nonneg _).trans (hdec 0 0 (0, (0, 0)) (0, (0, 0)))
    exact nonneg_of_mul_nonneg_left h1 (Real.exp_pos _)
  have hCf0 : 0 ≤ Cf := hCm0.trans hCf
  have herrK0 : 0 ≤ errK := by
    refine le_trans ?_ herrK
    have := Real.exp_pos (-(cm * ((4 * (R + 1) : ℕ) : ℝ)))
    have := Real.exp_pos (-(cm * ((R : ℝ) - 1)))
    positivity
  set sites : (Fin 4 → ℤ) → Finset (TorusSite (boxSide ℓ.side K k)) := fun v => weightSupportSites ℓ.side k (boxSide ℓ.side K k) (unitTorusWeight ℓ.side K k (translateBy ℓ.side K k v g)) with hsites
  refine ⟨fun v y p p' => if y ∈ sites v then κs v y p p' else 0,
    fun v => ∑ z, coldResponseChain ℓ β (flowCouplings ℓ β) al k (boxSide ℓ.side K k) z (trivialField (boxSide ℓ.side K k)) (unitTorusWeight ℓ.side K k (translateBy ℓ.side K k v g)), ?_, ?_⟩
  · intro v _
    refine ⟨fun y p p' => ?_, fun y p p' => ?_, fun y hy p p' => ?_, fun y μ ν ρ τ hμ hρ => ?_⟩
    · by_cases hy : y ∈ sites v
      · simp only [if_pos hy]
        exact hsym v y p p'
      · simp only [if_neg hy]
    · by_cases hy : y ∈ sites v
      · simp only [if_pos hy]
        refine (hdec v y p p').trans ?_
        have hm0 : 0 ≤ max (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ) := le_max_of_le_left (Nat.cast_nonneg _)
        have h1 : Real.exp (-(cm * max (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ))) ≤
            Real.exp (-(cc * max (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ))) := by
          apply Real.exp_le_exp.mpr
          have := mul_le_mul_of_nonneg_right hcc hm0
          linarith
        calc Cm * Real.exp (-(cm * max (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ))) ≤
              Cm * Real.exp (-(cc * max (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ))) := mul_le_mul_of_nonneg_left h1 hCm0
          _ ≤ Cf * Real.exp (-(cc * max (_root_.YangMills.Construction.TorusFields.supDist p.1 y : ℝ) (_root_.YangMills.Construction.TorusFields.supDist p'.1 y : ℝ))) :=
              mul_le_mul_of_nonneg_right hCf (Real.exp_pos _).le
      · simp only [if_neg hy, abs_zero]
        positivity
    · have hy' : y ∉ sites v := by
        intro hmem
        have := hy y hmem
        rw [_root_.YangMills.Construction.TorusFields.supDist_self] at this
        omega
      simp only [if_neg hy']
    · by_cases hy : y ∈ sites v
      · simp only [if_pos hy]
        refine (hpl v y μ ν ρ τ hμ hρ).trans (le_trans ?_ herrK)
        have h1 := (hw v).2.1
        have h2 : Cm * (3 * weightLipschitz ℓ.side k (unitTorusWeight ℓ.side K k (translateBy ℓ.side K k v g)) + Real.exp (-(cm * ((4 * (R + 1) : ℕ) : ℝ)))) ≤
            Cm * (3 * (2 / (vt * lengthInSites ℓ.side K k d)) + Real.exp (-(cm * ((4 * (R + 1) : ℕ) : ℝ)))) :=
          mul_le_mul_of_nonneg_left (by linarith) hCm0
        linarith
      · simp only [if_neg hy, Finset.sum_const_zero, zero_sub]
        have hz : blockMean ℓ.side k (boxSide ℓ.side K k) y (unitTorusWeight ℓ.side K k (translateBy ℓ.side K k v g)) = 0 := by
          obtain ⟨-, hlin, hread⟩ := hW ℓ.side hodd k (boxSide ℓ.side K k) y
          have h1 := hread (unitTorusWeight ℓ.side K k (translateBy ℓ.side K k v g)) (fun p => 0 * (unitTorusWeight ℓ.side K k (translateBy ℓ.side K k v g)) p + 0 * (unitTorusWeight ℓ.side K k (translateBy ℓ.side K k v g)) p) (fun p hp => by
            simp only [zero_mul, add_zero]
            by_contra hne
            exact hy (by
              simp only [hsites, weightSupportSites, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨p, hp, hne⟩))
          rw [h1, hlin]
          ring
        rw [hz]
        simp only [mul_zero, ite_self, neg_zero, abs_zero]
        exact herrK0
  · have hae : ∀ᵐ u ∂(markedSampleLaw T β k (boxSide ℓ.side K k)), ∀ v : Fin 4 → ℤ, ∃ F : TorusSite (boxSide ℓ.side K k) → ℝ,
        response T β al k (boxSide ℓ.side K k) (unitTorusWeight ℓ.side K k (translateBy ℓ.side K k v g)) u =
            ∑ z, F z + ∑ z, coldResponseChain ℓ β (flowCouplings ℓ β) al k (boxSide ℓ.side K k) z (trivialField (boxSide ℓ.side K k)) (unitTorusWeight ℓ.side K k (translateBy ℓ.side K k v g)) ∧
        (∀ z, z ∉ sites v → F z = 0) ∧
        ∀ (z : TorusSite (boxSide ℓ.side K k)) (n' : ℕ) [NeZero n'] (W' : TorusField n') (z' : TorusSite n') (m : ℕ)
          (ω' : (∅ : Finset (TorusSite n')) → (T.stage k).labels.Ω) (h' : PlaquetteWeight (fineSide ℓ.side k n')),
          ℓ.n₀ ≤ n' → IsCold ℓ.threshold W' →
          (clusterRange (flowCouplings ℓ β k) : ℝ) / 64 ≤ m →
          StatesAgreeNear ℓ (stageState T k (boxSide ℓ.side K k) u).1 W' (stageState T k (boxSide ℓ.side K k) u).2.1 ∅ (stageState T k (boxSide ℓ.side K k) u).2.2 ω' z z' m →
          WeightsAgreeAt ℓ.side k z z' (unitTorusWeight ℓ.side K k (translateBy ℓ.side K k v g)) h' →
          |F z - centeredResponse (coldResponseChain ℓ β (flowCouplings ℓ β) al k) n' z' W' h'| ≤
            Real.exp (-(cf * m)) * weightNorm ℓ.side k (unitTorusWeight ℓ.side K k (translateBy ℓ.side K k v g)) :=
      ae_all_iff.mpr fun v => hF _
    show ∀ᵐ u ∂(markedSampleLaw T β k (boxSide ℓ.side K k)), _
    filter_upwards [hae] with u hu hev v hv
    obtain ⟨F, hsum, hoff, hforget⟩ := hu v
    set q := stageState T k (boxSide ℓ.side K k) u with hq
    set hv' := unitTorusWeight ℓ.side K k (translateBy ℓ.side K k v g) with hhv
    have hp : ((outerData T k o R q, restrictInner o R q.1) : OuterData T k o R × InnerField o R) ∈ c.orbitSet := hev
    obtain ⟨γ, vv, bb, hγ, hb, -, hcv, hcl⟩ := hchart.gauge.bounds _ hp
    have hjoin : glueField (outerData T k o R q).1 (restrictInner o R q.1) = q.1 := glueField_restrict o R q.1
    simp only [hjoin] at hb hcv
    set A := chartConnection c u with hA
    set G : TorusSite (boxSide ℓ.side K k) → UnitQuaternion := c.axialGauge (outerData T k o R q) * γ with hG
    set S := plaquettesIn (supBall o (2 * (R : ℝ))) with hSdef
    set B₀ : ℝ := Real.exp (-(cf * (R : ℝ))) + Cm * (t ^ 3 + t * (2 * U) ^ 2 + Real.exp (-(cm * (R : ℝ)))) with hB₀
    have hdis : Disjoint q.2.1 (supBall o (3 * (R : ℝ))) := hchart.support_disjoint u hev
    have hsize : weightNorm ℓ.side k hv' ≤ 1 := by
      unfold weightNorm
      refine max_le (hw v).1 ?_
      have := (hw v).2.1
      linarith
    have hsite_bound : ∀ y ∈ sites v, |F y - (1 / 2) * ∑ p ∈ S, ∑ p' ∈ S, κs v y p p' * curlPairing A p p'| ≤ B₀ := by
      intro y hy
      have hyo : (_root_.YangMills.Construction.TorusFields.supDist y o : ℝ) ≤ (R : ℝ) / 8 := by
        have h1 := hnear v hv hy
        simpa [supBall] using h1
      have hbox : ∀ (w : TorusSite (boxSide ℓ.side K k)) (r : ℕ), r ≤ R + 1 → _root_.YangMills.Construction.TorusFields.supDist w y ≤ r → (_root_.YangMills.Construction.TorusFields.supDist w o : ℝ) ≤ (r : ℝ) + (R : ℝ) / 8 := by
        intro w r _ hw'
        have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle w y o
        have h2 : (_root_.YangMills.Construction.TorusFields.supDist w o : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist w y : ℝ) + (_root_.YangMills.Construction.TorusFields.supDist y o : ℝ) := by exact_mod_cast h1
        have h3 : (_root_.YangMills.Construction.TorusFields.supDist w y : ℝ) ≤ r := by exact_mod_cast hw'
        linarith
      have hbox2 : ∀ w : TorusSite (boxSide ℓ.side K k), _root_.YangMills.Construction.TorusFields.supDist w y ≤ R + 1 → w ∈ supBall o (2 * (R : ℝ)) := by
        intro w hw'
        have h1 := hbox w (R + 1) le_rfl hw'
        simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and]
        push_cast at h1
        linarith
      have H3 : ∀ (a : Fin 4 → ℤ) (μ ν : Fin 4), μ ≠ ν → (∀ dd ∈ plaquetteOffsets μ ν, OffsetInBox (R + 1) (a + dd)) →
          curvature q.1 (y + siteOfInt a) μ ν ≤ t := by
        have base : ∀ (a : Fin 4 → ℤ) (μ ν : Fin 4), μ < ν → (∀ z ∈ plaquetteVertices (y + siteOfInt a) μ ν, _root_.YangMills.Construction.TorusFields.supDist z y ≤ R + 1) →
            curvature q.1 (y + siteOfInt a) μ ν ≤ t := by
          intro a μ ν hlt hc
          have hmem : ((y + siteOfInt a, μ, ν) : TorusPlaquette (boxSide ℓ.side K k)) ∈ S := mem_plaquettesIn'.mpr ⟨hlt, fun z hz => hbox2 z (hc z hz)⟩
          exact (hcv _ hmem).trans ht
        intro a μ ν hne hc
        have hcor : ∀ z ∈ plaquetteVertices (y + siteOfInt a) μ ν, _root_.YangMills.Construction.TorusFields.supDist z y ≤ R + 1 := by
          intro z hz
          obtain ⟨dd, hdd, rfl⟩ := (mem_plaquetteVertices_iff_offset _ _ _ _).mp hz
          rw [add_assoc, ← siteOfInt_add, _root_.YangMills.Construction.TorusFields.supDist_comm]
          refine supDist_add_siteOfInt_le _ _ _ fun i => ?_
          have h1 := hc dd hdd i
          rw [Int.abs_eq_natAbs] at h1
          exact_mod_cast h1
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact base a μ ν hlt hcor
        · rw [curvature_swap]
          refine base a ν μ hlt fun z hz => hcor z ?_
          simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
          rcases hz with rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inr (add_right_comm _ _ _)))
      have H2 : ∀ b : TorusBond (boxSide ℓ.side K k), _root_.YangMills.Construction.TorusFields.supDist b.1 y ≤ R → ‖(A b : Quaternion ℝ)‖ ≤ 2 * U ∧
          ‖(A b : Quaternion ℝ) - (minimalLog (TorusFields.gaugeTransform G q.1 b.1 b.2) : Quaternion ℝ)‖ ≤ (2 * U) ^ 2 := by
        intro b hbd
        have hb2 : _root_.YangMills.Construction.TorusFields.supDist (b.1 + unitStep _ b.2) y ≤ R + 1 := by
          have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle (b.1 + unitStep _ b.2) b.1 y
          have h2 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le b.1 b.2
          rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at h2
          omega
        have hbS : b ∈ bondsWithin (supBall o (2 * (R : ℝ))) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbox2 _ (by omega), hbox2 _ hb2⟩
        obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hb b hbS
        have hAb : A b = c.background (outerData T k o R q) b + c.coord (outerData T k o R q) (restrictInner o R q.1) b := rfl
        have hvA : vv b = A b + bb b := by rw [e2, hAb]
        have hv1 : ‖(vv b : Quaternion ℝ)‖ ≤ U := e4.trans hU
        have hleast : minimalLog (expUnit (vv b)) = vv b :=
          minimalLog_expUnit _ (by linarith [Real.pi_gt_three])
        have hG' : TorusFields.gaugeTransform G q.1 b.1 b.2 = expUnit (vv b) := e1
        rw [hG', hleast]
        have h5 := e5.trans hU
        have h6 := e6.trans hU
        constructor
        · calc ‖(A b : Quaternion ℝ)‖ = ‖A b‖ := rfl
            _ ≤ ‖c.background (outerData T k o R q) b‖ + ‖c.coord (outerData T k o R q) (restrictInner o R q.1) b‖ := by
              rw [hAb]
              exact norm_add_le _ _
            _ ≤ 2 * U := by linarith
        · have h7 : (A b : Quaternion ℝ) - (vv b : Quaternion ℝ) = -(bb b : Quaternion ℝ) := by
            rw [hvA, Submodule.coe_add]
            abel
          rw [h7, norm_neg]
          have h8 : ‖c.background (outerData T k o R q) b‖ ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h5 2
          have h9 : ‖c.coord (outerData T k o R q) (restrictInner o R q.1) b‖ ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h6 2
          calc ‖(bb b : Quaternion ℝ)‖ = ‖bb b‖ := rfl
            _ ≤ 2 * (‖c.background (outerData T k o R q) b‖ ^ 2 + ‖c.coord (outerData T k o R q) (restrictInner o R q.1) b‖ ^ 2) := e3
            _ ≤ (2 * U) ^ 2 := by nlinarith
      have hSsub : plaquettesIn (supBall y (R : ℝ)) ⊆ S := by
        intro p hp'
        obtain ⟨h1, h2⟩ := mem_plaquettesIn'.mp hp'
        exact mem_plaquettesIn'.mpr ⟨h1, fun z hz => hbox2 z ((mem_supBall_natCast.mp (h2 z hz)).trans (by omega))⟩
      have H4 : ∀ p ∈ plaquettesIn (supBall y (R : ℝ)), ‖(lieFormCurl A p : Quaternion ℝ)‖ ≤ t := by
        intro p hp'
        have h1 : ‖lieFormCurl A p‖ ^ 2 ≤ curlNormSq (supBall o (2 * (R : ℝ))) A :=
          Finset.single_le_sum (f := fun p => ‖lieFormCurl A p‖ ^ 2) (fun _ _ => sq_nonneg _) (hSsub hp')
        have h2 : ‖lieFormCurl A p‖ ^ 2 ≤ t ^ 2 := h1.trans ((show curlNormSq (supBall o (2 * (R : ℝ))) A ≤ _ from hcl).trans hct)
        exact (abs_le_of_sq_le_sq' h2 ht0).2
      have hMk := hform v y q.1 G A (2 * U) t (by positivity) hU1 ht0 ht1 hts H3 H2 H4 S hSsub
      have hcurvM := curvature_mirrorField_le (m := R + 1) (by omega) y q.1 ht0 H3
      have hcold : IsCold ℓ.threshold (mirrorField (R + 1) y q.1) := fun z μ ν _ => (hcurvM z μ ν).trans_lt hts
      have hnotY : ∀ a : Fin 4 → ℤ, OffsetInBox R a → y + siteOfInt a ∉ q.2.1 := by
        intro a ha hmem
        refine Finset.disjoint_left.mp hdis hmem ?_
        have h1 : _root_.YangMills.Construction.TorusFields.supDist (y + siteOfInt a) y ≤ R := by
          rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
          refine supDist_add_siteOfInt_le _ _ _ fun i => ?_
          have h2 := ha i
          rw [Int.abs_eq_natAbs] at h2
          exact_mod_cast h2
        have h2 := hbox _ R (by omega) h1
        simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and]
        linarith
      have hmono : ∀ a : Fin 4 → ℤ, OffsetInBox R a → OffsetInBox (R + 1) a := fun a ha i =>
        (ha i).trans (by push_cast; omega)
      have ω' : (∅ : Finset (TorusSite (4 * (R + 1)))) → (T.stage k).labels.Ω := fun z => (Finset.notMem_empty _ z.2).elim
      have hstates : StatesAgreeNear ℓ q.1 (mirrorField (R + 1) y q.1) q.2.1 ∅ q.2.2 ω' y 0 R := by
        refine ⟨by omega, by omega, ?_, ?_, ?_, ?_⟩
        · intro b hb'
          have h1 := mirrorField_siteOfInt (by omega : 2 ≤ R + 1) y q.1 b ⟨hmono _ hb'.1, hmono _ hb'.2⟩
          show q.1 (y + siteOfInt b.1) b.2 = mirrorField (R + 1) y q.1 (0 + siteOfInt b.1) b.2
          rw [zero_add, h1]
        · intro a ha
          exact ⟨fun h => absurd h (hnotY a ha), fun h => absurd h (by simp)⟩
        · intro a _ _ hz'
          exact absurd hz' (by simp)
        · rintro ⟨a, ha, hmem⟩
          exact absurd hmem (hnotY a ha)
      have hr' : (clusterRange (flowCouplings ℓ β k) : ℝ) / 64 ≤ ((R : ℕ) : ℝ) := by
        rw [hxk]
        exact hr
      have hfg := hforget y (4 * (R + 1)) (mirrorField (R + 1) y q.1) 0 R ω' (H v y) hRn hcold hr' hstates (hag v y)
      have hfg' : |F y - centeredResponse (coldResponseChain ℓ β (flowCouplings ℓ β) al k) (4 * (R + 1)) 0 (mirrorField (R + 1) y q.1) (H v y)| ≤
          Real.exp (-(cf * (R : ℝ))) :=
        hfg.trans (mul_le_of_le_one_right (Real.exp_pos _).le hsize)
      have h3 := abs_sub_le (F y) (centeredResponse (coldResponseChain ℓ β (flowCouplings ℓ β) al k) (4 * (R + 1)) 0 (mirrorField (R + 1) y q.1) (H v y))
        ((1 / 2) * ∑ p ∈ S, ∑ p' ∈ S, κs v y p p' * curlPairing A p p')
      linarith
    have hkern : ∑ p ∈ S, ∑ p' ∈ S, totalKernel (fun y p p' => if y ∈ sites v then κs v y p p' else 0) p p' *
          curlPairing A p p' =
        ∑ y, ∑ p ∈ S, ∑ p' ∈ S, (if y ∈ sites v then κs v y p p' else 0) * curlPairing A p p' := by
      unfold totalKernel
      simp only [Finset.sum_mul]
      calc _ = ∑ p ∈ S, ∑ y, ∑ p' ∈ S, (if y ∈ sites v then κs v y p p' else 0) * curlPairing A p p' :=
            Finset.sum_congr rfl fun p _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    have hresp : boxResponse T β al K k (translateBy ℓ.side K k v g) u =
        ∑ z, F z + ∑ z, coldResponseChain ℓ β (flowCouplings ℓ β) al k (boxSide ℓ.side K k) z (trivialField (boxSide ℓ.side K k)) hv' := hsum
    show |boxResponse T β al K k (translateBy ℓ.side K k v g) u -
        ∑ z, coldResponseChain ℓ β (flowCouplings ℓ β) al k (boxSide ℓ.side K k) z (trivialField (boxSide ℓ.side K k)) hv' -
        (1 / 2) * ∑ p ∈ S, ∑ p' ∈ S, totalKernel (fun y p p' => if y ∈ sites v then κs v y p p' else 0) p p' *
          curlPairing A p p'| ≤ err
    rw [hresp, hkern, add_sub_cancel_right, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have hzero : ∀ y ∈ (Finset.univ : Finset (TorusSite (boxSide ℓ.side K k))), y ∉ sites v →
        F y - (1 / 2) * ∑ p ∈ S, ∑ p' ∈ S, (if y ∈ sites v then κs v y p p' else 0) * curlPairing A p p' = 0 := by
      intro y _ hy
      simp only [if_neg hy, zero_mul, Finset.sum_const_zero, mul_zero, sub_zero]
      exact hoff y hy
    rw [← Finset.sum_subset (Finset.subset_univ (sites v)) hzero]
    have hB0 : 0 ≤ B₀ := by
      have := Real.exp_pos (-(cf * (R : ℝ)))
      have := Real.exp_pos (-(cm * (R : ℝ)))
      rw [hB₀]
      positivity
    have hcard := (hw v).2.2
    calc |∑ y ∈ sites v, (F y - (1 / 2) * ∑ p ∈ S, ∑ p' ∈ S, (if y ∈ sites v then κs v y p p' else 0) * curlPairing A p p')|
        ≤ ∑ y ∈ sites v, |F y - (1 / 2) * ∑ p ∈ S, ∑ p' ∈ S, (if y ∈ sites v then κs v y p p' else 0) * curlPairing A p p'| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _y ∈ sites v, B₀ := by
          refine Finset.sum_le_sum fun y hy => ?_
          simp only [if_pos hy]
          exact hsite_bound y hy
      _ = ((sites v).card : ℝ) * B₀ := by simp
      _ ≤ (4 * lengthInSites ℓ.side K k d + 11) ^ 4 * B₀ := mul_le_mul_of_nonneg_right hcard hB0
      _ ≤ err := herr
private def couplingThreshold (ℓ : StepParameters) (Xi vt C' cm cf xm xf : ℝ) : ℝ :=
  max (Real.exp 1) <| max xm <| max xf <| max ((81 / cm) ^ (1 / (1 / 54 : ℝ))) <| max ((81 / cf) ^ (1 / (1 / 54 : ℝ))) <|
  max ((160 * (2 * C')) ^ (1 / (26 / 90 : ℝ))) <| max ((160 * (2 * C' / ℓ.threshold)) ^ (1 / (26 / 90 : ℝ))) <|
  max ((16 : ℝ) ^ (1 / ((1 : ℝ) / 27))) <| max ((ℓ.n₀ : ℝ) ^ (1 / ((1 : ℝ) / 27))) <|
  max ((|Xi| + 8 * |ℓ.B| + 1) ^ (1 / (26 / 27 : ℝ))) ((6 / vt) ^ (1 / ((1 : ℝ) / 100)))
private theorem kernelError_le {Cm cm w Cf : ℝ} {R : ℕ} (hcm : 0 < cm) (hw0 : 0 < w) (hR : 1 ≤ R)
    (hf : 8 * |Cm| + |Cm| * (256 * 8 ^ 8 * ((Nat.factorial 8 : ℝ) * (2 / cm) ^ 8) * Real.exp cm) ≤ Cf) :
    Cm * (6 * w + Real.exp (-(cm * ((4 * (R + 1) : ℕ) : ℝ)))) +
      (16 * (((4 * (R + 1) : ℕ) : ℝ)) ^ 4) ^ 2 * (Cm * Real.exp (-(cm * ((R : ℝ) - 1)))) ≤
      Cf * (w + Real.exp (-(cm / 2 * (R : ℝ)))) := by
  have hRr : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  set D : ℝ := |Cm| with hD
  have hD0 : 0 ≤ D := abs_nonneg _
  have hCmD : Cm ≤ D := le_abs_self _
  set Aₜ : ℝ := 256 * 8 ^ 8 * ((Nat.factorial 8 : ℝ) * (2 / cm) ^ 8) * Real.exp cm with hAt
  set E := Real.exp (-(cm / 2 * (R : ℝ))) with hEdef
  have e2 : Real.exp (-(cm * ((4 * (R + 1) : ℕ) : ℝ))) ≤ E := by
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have e3 : (16 * (((4 * (R + 1) : ℕ) : ℝ)) ^ 4) ^ 2 * Real.exp (-(cm * ((R : ℝ) - 1))) ≤ Aₜ * E := by
    have hM : (((4 * (R + 1) : ℕ) : ℝ)) ≤ 8 * (R : ℝ) := by
      push_cast
      linarith
    have hM8 : (((4 * (R + 1) : ℕ) : ℝ)) ^ 8 ≤ 8 ^ 8 * (R : ℝ) ^ 8 := by
      calc (((4 * (R + 1) : ℕ) : ℝ)) ^ 8 ≤ (8 * (R : ℝ)) ^ 8 := pow_le_pow_left₀ (Nat.cast_nonneg _) hM 8
        _ = 8 ^ 8 * (R : ℝ) ^ 8 := by ring
    have hP := pow_eight_le_exp hcm (R : ℝ) (Nat.cast_nonneg _)
    have hsplit : Real.exp (cm / 2 * (R : ℝ)) * Real.exp (-(cm * ((R : ℝ) - 1))) = Real.exp cm * E := by
      rw [← Real.exp_add, hEdef, ← Real.exp_add]
      congr 1
      ring
    calc (16 * (((4 * (R + 1) : ℕ) : ℝ)) ^ 4) ^ 2 * Real.exp (-(cm * ((R : ℝ) - 1)))
        = 256 * (((4 * (R + 1) : ℕ) : ℝ)) ^ 8 * Real.exp (-(cm * ((R : ℝ) - 1))) := by ring
      _ ≤ 256 * (8 ^ 8 * ((Nat.factorial 8 : ℝ) * (2 / cm) ^ 8 * Real.exp (cm / 2 * (R : ℝ)))) *
            Real.exp (-(cm * ((R : ℝ) - 1))) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          refine mul_le_mul_of_nonneg_left (hM8.trans ?_) (by norm_num)
          exact mul_le_mul_of_nonneg_left hP (by positivity)
      _ = 256 * 8 ^ 8 * ((Nat.factorial 8 : ℝ) * (2 / cm) ^ 8) *
            (Real.exp (cm / 2 * (R : ℝ)) * Real.exp (-(cm * ((R : ℝ) - 1)))) := by ring
      _ = Aₜ * E := by rw [hsplit, hAt]; ring
  have e4 : Cm * (6 * w + Real.exp (-(cm * ((4 * (R + 1) : ℕ) : ℝ)))) ≤ D * (6 * w + E) := by
    have h1 : 0 ≤ 6 * w + Real.exp (-(cm * ((4 * (R + 1) : ℕ) : ℝ))) := by positivity
    calc Cm * (6 * w + Real.exp (-(cm * ((4 * (R + 1) : ℕ) : ℝ)))) ≤
          D * (6 * w + Real.exp (-(cm * ((4 * (R + 1) : ℕ) : ℝ)))) := mul_le_mul_of_nonneg_right hCmD h1
      _ ≤ D * (6 * w + E) := mul_le_mul_of_nonneg_left (by linarith) hD0
  have e5 : (16 * (((4 * (R + 1) : ℕ) : ℝ)) ^ 4) ^ 2 * (Cm * Real.exp (-(cm * ((R : ℝ) - 1)))) ≤ D * (Aₜ * E) := by
    have h1 : 0 ≤ (16 * (((4 * (R + 1) : ℕ) : ℝ)) ^ 4) ^ 2 * Real.exp (-(cm * ((R : ℝ) - 1))) := by positivity
    calc (16 * (((4 * (R + 1) : ℕ) : ℝ)) ^ 4) ^ 2 * (Cm * Real.exp (-(cm * ((R : ℝ) - 1))))
        = Cm * ((16 * (((4 * (R + 1) : ℕ) : ℝ)) ^ 4) ^ 2 * Real.exp (-(cm * ((R : ℝ) - 1)))) := by ring
      _ ≤ D * ((16 * (((4 * (R + 1) : ℕ) : ℝ)) ^ 4) ^ 2 * Real.exp (-(cm * ((R : ℝ) - 1)))) :=
          mul_le_mul_of_nonneg_right hCmD h1
      _ ≤ D * (Aₜ * E) := mul_le_mul_of_nonneg_left e3 hD0
  have e6 : D * (6 * w + E) + D * (Aₜ * E) ≤ (8 * D + D * Aₜ) * (w + E) := by
    have hq2 : 0 ≤ D * Aₜ * w := by positivity
    have hq3 : 0 ≤ D * w := by positivity
    have hq4 : 0 ≤ D * E := by positivity
    nlinarith
  have e7 : (8 * D + D * Aₜ) * (w + E) ≤ Cf * (w + E) := mul_le_mul_of_nonneg_right hf (by positivity)
  linarith
private theorem responseError_le {Cm cm cf n Rr δ C' Cf E : ℝ} (hn1 : 1 ≤ n) (hR : 1 ≤ Rr) (hδ : 0 ≤ δ) (hC' : 0 ≤ C')
    (hf : 15 ^ 4 * (1 + |Cm| * (5 * C' ^ 3 + 1)) ≤ Cf)
    (z1 : Real.exp (-(cf * Rr)) ≤ Rr ^ 8 * δ ^ 3) (z2 : Real.exp (-(cm * Rr)) ≤ Rr ^ 8 * δ ^ 3) (hE : 0 ≤ E) :
    (4 * n + 11) ^ 4 * (Real.exp (-(cf * Rr)) + Cm * ((C' * Rr ^ 2 * δ) ^ 3 + (C' * Rr ^ 2 * δ) * (2 * (C' * Rr ^ 3 * δ)) ^ 2 +
      Real.exp (-(cm * Rr)))) ≤ Cf * n ^ 4 * Rr ^ 8 * δ ^ 3 + E := by
  set Z : ℝ := Rr ^ 8 * δ ^ 3 with hZ
  have hZ0 : 0 ≤ Z := by positivity
  set D : ℝ := |Cm| with hD
  have hD0 : 0 ≤ D := abs_nonneg _
  have hCmD : Cm ≤ D := le_abs_self _
  set t : ℝ := C' * Rr ^ 2 * δ with ht
  set U : ℝ := C' * Rr ^ 3 * δ with hU
  have z3 : t ^ 3 ≤ C' ^ 3 * Z := by
    have h1 : Rr ^ 6 ≤ Rr ^ 8 := pow_le_pow_right₀ hR (by norm_num)
    calc t ^ 3 = C' ^ 3 * (Rr ^ 6 * δ ^ 3) := by rw [ht]; ring
      _ ≤ C' ^ 3 * (Rr ^ 8 * δ ^ 3) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have z4 : t * (2 * U) ^ 2 = 4 * C' ^ 3 * Z := by
    rw [ht, hU, hZ]
    ring
  have hb : Real.exp (-(cf * Rr)) + Cm * (t ^ 3 + t * (2 * U) ^ 2 + Real.exp (-(cm * Rr))) ≤ (1 + D * (5 * C' ^ 3 + 1)) * Z := by
    have h1 : 0 ≤ t ^ 3 + t * (2 * U) ^ 2 + Real.exp (-(cm * Rr)) := by positivity
    have h2 : Cm * (t ^ 3 + t * (2 * U) ^ 2 + Real.exp (-(cm * Rr))) ≤
        D * (t ^ 3 + t * (2 * U) ^ 2 + Real.exp (-(cm * Rr))) := mul_le_mul_of_nonneg_right hCmD h1
    have h3 : D * (t ^ 3 + t * (2 * U) ^ 2 + Real.exp (-(cm * Rr))) ≤ D * ((5 * C' ^ 3 + 1) * Z) := by
      refine mul_le_mul_of_nonneg_left ?_ hD0
      rw [z4]
      nlinarith
    nlinarith
  have hn15 : (4 * n + 11) ^ 4 ≤ 15 ^ 4 * n ^ 4 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hP : 0 ≤ (1 + D * (5 * C' ^ 3 + 1)) * Z := by positivity
  have hn4 : 0 ≤ n ^ 4 := by positivity
  have hleft : (4 * n + 11) ^ 4 * (Real.exp (-(cf * Rr)) + Cm * (t ^ 3 + t * (2 * U) ^ 2 + Real.exp (-(cm * Rr)))) ≤
      15 ^ 4 * n ^ 4 * ((1 + D * (5 * C' ^ 3 + 1)) * Z) :=
    (mul_le_mul_of_nonneg_left hb (by positivity)).trans (mul_le_mul_of_nonneg_right hn15 hP)
  have hfin : 15 ^ 4 * n ^ 4 * ((1 + D * (5 * C' ^ 3 + 1)) * Z) ≤ Cf * n ^ 4 * Z := by
    have h2 := mul_le_mul_of_nonneg_right hf (mul_nonneg hn4 hZ0)
    calc 15 ^ 4 * n ^ 4 * ((1 + D * (5 * C' ^ 3 + 1)) * Z)
        = 15 ^ 4 * (1 + D * (5 * C' ^ 3 + 1)) * (n ^ 4 * Z) := by ring
      _ ≤ Cf * (n ^ 4 * Z) := h2
      _ = Cf * n ^ 4 * Z := by ring
  have hz : Cf * n ^ 4 * Rr ^ 8 * δ ^ 3 = Cf * n ^ 4 * Z := by
    rw [hZ]
    ring
  rw [hz]
  linarith
set_option maxHeartbeats 1600000 in
private theorem exists_kernelFamilies_at_parameters (Tb : ParameterAssignment) (y : ℝ) (hdrawn : Tb.Admissible) (hRet : ExpansionReturnsAt (Tb.stepParameters y))
    (hWil : ∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β))
    (hodd : Odd (Tb.stepParameters y).side) (hE : weightExtensionStatement) (hN : WeightsCloseToBlockMeans)
    (hT : WeightsCompatibleAcrossTori) (hS : unitTorusWeightSizesStatement) (hW : BlockMeanIsLinearAndLocal)
    (Kr : ResponseParameters) {Cm cm xm cf xf : ℝ} (hmark : HasCurvedFieldResponse (Tb.stepParameters y) Kr Cm cm xm) (hcm : 0 < cm) (hcf : 0 < cf)
    (hFg : ∀ (T : StageTower (Tb.stepParameters y)) (S : FreeEnergies.ScoredStageTower T) (β : ℝ) (k tp : ℕ), k ≤ tp → S.params = Kr →
      S.FollowsFlow β tp → (∀ j ≤ k, (Tb.stepParameters y).y₁ ≤ flowCouplings (Tb.stepParameters y) β j) → xf ≤ flowCouplings (Tb.stepParameters y) β k →
      ∀ (n : ℕ) [NeZero n], IsBlockTorusSide (Tb.stepParameters y) n →
      ∀ h : PlaquetteWeight (fineSide (Tb.stepParameters y).side k n), ∀ᵐ u ∂(markedSampleLaw T β k n), ∃ F : TorusSite n → ℝ,
        response T β S.coeffs k n h u =
            ∑ z, F z + ∑ z, coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) S.coeffs k n z (trivialField n) h ∧
        (∀ z, z ∉ weightSupportSites (Tb.stepParameters y).side k n h → F z = 0) ∧
        ∀ (z : TorusSite n) (n' : ℕ) [NeZero n'] (W' : TorusField n') (z' : TorusSite n') (m : ℕ)
          (ω' : (∅ : Finset (TorusSite n')) → (T.stage k).labels.Ω) (h' : PlaquetteWeight (fineSide (Tb.stepParameters y).side k n')),
          (Tb.stepParameters y).n₀ ≤ n' → IsCold (Tb.stepParameters y).threshold W' →
          (clusterRange (flowCouplings (Tb.stepParameters y) β k) : ℝ) / 64 ≤ m →
          StatesAgreeNear (Tb.stepParameters y) (stageState T k n u).1 W' (stageState T k n u).2.1 ∅ (stageState T k n u).2.2 ω' z z' m →
          WeightsAgreeAt (Tb.stepParameters y).side k z z' h h' →
          |F z - centeredResponse (coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) S.coeffs k) n' z' W' h'| ≤
            Real.exp (-(cf * m)) * weightNorm (Tb.stepParameters y).side k h)
    {Xi : ℝ} (hXi : (Tb.stepParameters y).y₁ + 2 * (Tb.stepParameters y).B ≤ Xi)
    (hLv : ∀ d : ℝ, 0 < d → d < 1 → ∀ (K : ℕ) (β : ℝ), IsFlowDatum (Tb.stepParameters y) Xi K β → minimalCutoff (Tb.stepParameters y) Xi d ≤ K →
      IsSeparatedAt (Tb.stepParameters y) β K d (separationLevel (Tb.stepParameters y) β K d) ∧ separationLevel (Tb.stepParameters y) β K d < K ∧
      lengthInSites (Tb.stepParameters y).side K (separationLevel (Tb.stepParameters y) β K d) d ≤
        2 ^ 13 * ((Tb.stepParameters y).side : ℝ) * (clusterRange (couplingAtSeparation (Tb.stepParameters y) β K d) : ℝ))
    (hCp : ∀ X : ℝ, ∃ d₁ : ℝ, 0 < d₁ ∧ ∀ d : ℝ, 0 < d → d ≤ d₁ → ∀ (K : ℕ) (β : ℝ), IsFlowDatum (Tb.stepParameters y) Xi K β →
      minimalCutoff (Tb.stepParameters y) Xi d ≤ K → X ≤ couplingAtSeparation (Tb.stepParameters y) β K d)
    (hNear : ∀ (β : ℝ) (k : ℕ) (al : ℕ → ℝ), (∀ j ≤ k, y ≤ flowCouplings (Tb.stepParameters y) β j) →
      IsChainResponseCoeff (Tb.stepParameters y) Kr β k al → |al k - 1| ≤ 1 / 4)
    {vt : ℝ} (hvt0 : 0 < vt) (hvt1 : vt ≤ 1) (C₁ : ℝ) (Cj xp : ℕ → ℝ) :
    ∃ C cc d₀ : ℝ, 0 < cc ∧ 0 < d₀ ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ →
    ∀ (K : ℕ) (β : ℝ) (al : ℕ → ℝ) (T : StageTower (Tb.stepParameters y)), IsStateChain Tb y Kr Xi d K β al T →
    ∀ (k m R : ℕ) (x : ℝ), k = separationLevel (Tb.stepParameters y) β K d → x = couplingAtSeparation (Tb.stepParameters y) β K d →
    R = boxRadius x → m = averagingRadius x → ∀ (f h : AmbientSpace → ℝ), IsNormalizedTestPair d vt f h →
    ∀ (o : TorusSite (boxSide (Tb.stepParameters y).side K k)), IsLocalizedNear (Tb.stepParameters y).side K k m R o f →
    IsLocalizedNear (Tb.stepParameters y).side K k m R o h →
    ∀ (c : BoxChart T k o R) (c₀ ε φ₀ : ℝ), IsGoodChart T β K k c x C₁ c₀ ε φ₀ Cj xp →
      ∃ (κ κ' : (Fin 4 → ℤ) → TorusSite (boxSide (Tb.stepParameters y).side K k) → TorusPlaquette (boxSide (Tb.stepParameters y).side K k) →
          TorusPlaquette (boxSide (Tb.stepParameters y).side K k) → ℝ) (κ₀ κ₀' : (Fin 4 → ℤ) → ℝ),
        IsBoxKernelFamily T β al K k m c C cc
            (C * ((vt * lengthInSites (Tb.stepParameters y).side K k d)⁻¹ + Real.exp (-(cc * R))))
            (C * lengthInSites (Tb.stepParameters y).side K k d ^ 4 * (R : ℝ) ^ 8 * boxScale x ^ 3 + Real.exp (-(cc * R)))
            (fun v => translateBy (Tb.stepParameters y).side K k v f) κ κ₀ ∧
        IsBoxKernelFamily T β al K k m c C cc
            (C * ((vt * lengthInSites (Tb.stepParameters y).side K k d)⁻¹ + Real.exp (-(cc * R))))
            (C * lengthInSites (Tb.stepParameters y).side K k d ^ 4 * (R : ℝ) ^ 8 * boxScale x ^ 3 + Real.exp (-(cc * R)))
            (fun v => translateBy (Tb.stepParameters y).side K k v h) κ' κ₀' := by
  have hσ : 0 < (Tb.stepParameters y).threshold := hdrawn.σ_pos
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = max C₁ 1 := ⟨_, rfl⟩
  have hC'1 : 1 ≤ C' := hC' ▸ le_max_right _ _
  have hC₁C' : C₁ ≤ C' := hC' ▸ le_max_left _ _
  have hC'0 : 0 < C' := by linarith
  obtain ⟨Cf, hCfdef⟩ : ∃ Cf : ℝ, Cf = (8 * |Cm| + |Cm| * (256 * 8 ^ 8 * ((Nat.factorial 8 : ℝ) * (2 / cm) ^ 8) * Real.exp cm)) +
      15 ^ 4 * (1 + |Cm| * (5 * C' ^ 3 + 1)) := ⟨_, rfl⟩
  have hAt0 : 0 ≤ |Cm| * (256 * 8 ^ 8 * ((Nat.factorial 8 : ℝ) * (2 / cm) ^ 8) * Real.exp cm) := by positivity
  have hD0 : 0 ≤ |Cm| := abs_nonneg _
  have hP0 : 0 ≤ 15 ^ 4 * (1 + |Cm| * (5 * C' ^ 3 + 1)) := by positivity
  have hCf1 : 8 * |Cm| + |Cm| * (256 * 8 ^ 8 * ((Nat.factorial 8 : ℝ) * (2 / cm) ^ 8) * Real.exp cm) ≤ Cf := by
    rw [hCfdef]
    linarith
  have hCf2 : 15 ^ 4 * (1 + |Cm| * (5 * C' ^ 3 + 1)) ≤ Cf := by
    rw [hCfdef]
    linarith
  have hCmCf : Cm ≤ Cf := by
    have := le_abs_self Cm
    linarith
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = couplingThreshold (Tb.stepParameters y) Xi vt C' cm cf xm xf := ⟨_, rfl⟩
  obtain ⟨d₁, hd₁, hcp⟩ := hCp X
  refine ⟨Cf, cm / 2, min (1 / 4) d₁, by positivity, lt_min (by norm_num) hd₁, ?_⟩
  intro d hd0 hdle K β al T hch k m R x hk hx hRdef hmdef f h hpair o hnf hnh c c₀ ε φ₀ hchart
  have hdq : d ≤ 1 / 4 := hdle.trans (min_le_left _ _)
  have hdd₁ : d ≤ d₁ := hdle.trans (min_le_right _ _)
  obtain ⟨hfar, hkK, -⟩ := hLv d hd0 (by linarith) K β hch.isFlowDatum hch.minimalCutoff_le
  rw [← hk] at hfar hkK
  have hxX : X ≤ x := by
    rw [hx]
    exact hcp d hd0 hdd₁ K β hch.isFlowDatum hch.minimalCutoff_le
  have hxk : x = flowCouplings (Tb.stepParameters y) β k := by
    rw [hx, hk]
    rfl
  rw [hX] at hxX
  have fr : ∀ {a b : ℝ}, max a b ≤ x → a ≤ x ∧ b ≤ x := fun h => ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩
  obtain ⟨g1, g2⟩ := fr hxX
  obtain ⟨g3, g4⟩ := fr g2
  obtain ⟨g5, g6⟩ := fr g4
  obtain ⟨g7, g8⟩ := fr g6
  obtain ⟨g9, g10⟩ := fr g8
  obtain ⟨g11, g12⟩ := fr g10
  obtain ⟨g13, g14⟩ := fr g12
  obtain ⟨g15, g16⟩ := fr g14
  obtain ⟨g17, g18⟩ := fr g16
  obtain ⟨g19, g20⟩ := fr g18
  have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num)).trans g1
  have hx0 : 0 < x := by linarith
  have hδ0 := boxScale_nonneg hx1
  obtain ⟨hRl, hRu⟩ := boxRadius_bounds hx1
  have hRR : (R : ℝ) = (boxRadius x : ℝ) := by rw [hRdef]
  have hR16 : 16 ≤ R := by
    have h1 : (16 : ℝ) ≤ x ^ ((1 : ℝ) / 27) := le_rpow_of_rpow_inv_le (by norm_num) (by norm_num) g15
    have h2 : (16 : ℝ) ≤ (R : ℝ) := by rw [hRR]; linarith
    exact_mod_cast h2
  have hRr : (1 : ℝ) ≤ (R : ℝ) := by
    have : (16 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR16
    linarith
  have hRn₀ : (Tb.stepParameters y).n₀ ≤ R := by
    have h1 : ((Tb.stepParameters y).n₀ : ℝ) ≤ x ^ ((1 : ℝ) / 27) := le_rpow_of_rpow_inv_le (by norm_num) (by positivity) g17
    have h2 : ((Tb.stepParameters y).n₀ : ℝ) ≤ (R : ℝ) := by rw [hRR]; linarith
    exact_mod_cast h2
  have hRn : (Tb.stepParameters y).n₀ ≤ 4 * (R + 1) := by omega
  have h0 : HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β) := hWil β (hch.isFlowDatum.le_coupling 0 (Nat.zero_le _))
  have hL2 : 2 ≤ (Tb.stepParameters y).side := T.two_le_side
  have hwide := boxRadius_add_three_le_pow hRet h0 hch.isFlowDatum.le_coupling hch.isFlowDatum.coupling_le_top hkK hL2 hxk hx1 g19
  rw [← hRdef] at hwide
  have hpow : (Tb.stepParameters y).side ^ (K - k) = (Tb.stepParameters y).side ^ (K - k - 1) * (Tb.stepParameters y).side := by
    rw [← pow_succ]
    congr 1
    omega
  have hside : boxSide (Tb.stepParameters y).side K k = 2 * ((Tb.stepParameters y).side ^ (K - k - 1) * (Tb.stepParameters y).side) := by
    unfold boxSide
    rw [hpow]
  have hLP : 2 * ((Tb.stepParameters y).side ^ (K - k - 1)) ≤ (Tb.stepParameters y).side ^ (K - k - 1) * (Tb.stepParameters y).side := by
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ hL2
  have hNR : 2 * (R + 2) < boxSide (Tb.stepParameters y).side K k := by
    rw [hside]
    omega
  have hblock : IsBlockTorusSide (Tb.stepParameters y) (boxSide (Tb.stepParameters y).side K k) := by
    refine ⟨?_, ?_⟩
    · rw [hside]
      exact Dvd.dvd.mul_left (Dvd.intro_left _ rfl) 2
    · rw [hside]
      have h1 : (Tb.stepParameters y).n₀ ≤ (Tb.stepParameters y).side ^ (K - k - 1) := by omega
      have h2 := Nat.mul_le_mul_left (Tb.stepParameters y).side h1
      rw [mul_comm ((Tb.stepParameters y).side ^ (K - k - 1))]
      exact h2.trans (Nat.le_mul_of_pos_left _ (by norm_num))
  have hr1 : (clusterRange x : ℝ) ≤ (R : ℝ) := by
    have h1 : x ^ ((1 : ℝ) / 100) ≤ x ^ ((1 : ℝ) / 27) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have h2 : clusterRange x ≤ R := by
      rw [hRdef]
      unfold clusterRange boxRadius
      exact Nat.ceil_mono h1
    exact_mod_cast h2
  have hr : (clusterRange x : ℝ) / 64 ≤ R := by
    have : (0 : ℝ) ≤ (clusterRange x : ℝ) := Nat.cast_nonneg _
    linarith
  have hn : x ^ ((1 : ℝ) / 100) ≤ lengthInSites (Tb.stepParameters y).side K k d := by
    have h1 : (2 : ℝ) ^ 12 * (clusterRange (flowCouplings (Tb.stepParameters y) β k) : ℝ) ≤ lengthInSites (Tb.stepParameters y).side K k d := hfar
    rw [← hxk] at h1
    have h2 : x ^ ((1 : ℝ) / 100) ≤ (clusterRange x : ℝ) := Nat.le_ceil _
    have h3 : (0 : ℝ) ≤ (clusterRange x : ℝ) := Nat.cast_nonneg _
    linarith
  have hn6 : 6 / vt ≤ lengthInSites (Tb.stepParameters y).side K k d := (le_rpow_of_rpow_inv_le (by norm_num) (by positivity) g20).trans hn
  have hn1 : 1 ≤ lengthInSites (Tb.stepParameters y).side K k d := by
    refine le_trans ?_ hn6
    rw [le_div_iff₀ hvt0]
    linarith
  have hnpos : 0 < lengthInSites (Tb.stepParameters y).side K k d := by linarith
  have hvn : 6 ≤ vt * lengthInSites (Tb.stepParameters y).side K k d := by
    rw [div_le_iff₀ hvt0] at hn6
    linarith
  have hlip : 3 * (2 / (vt * lengthInSites (Tb.stepParameters y).side K k d)) ≤ 1 := by
    have hp : 0 < vt * lengthInSites (Tb.stepParameters y).side K k d := by positivity
    rw [show 3 * (2 / (vt * lengthInSites (Tb.stepParameters y).side K k d)) = 6 / (vt * lengthInSites (Tb.stepParameters y).side K k d) by ring, div_le_one hp]
    exact hvn
  have hR3 : 0 ≤ (R : ℝ) ^ 3 * boxScale x := by positivity
  have hR2 : 0 ≤ (R : ℝ) ^ 2 * boxScale x := by positivity
  have hU0 : 0 ≤ C' * (R : ℝ) ^ 3 * boxScale x := by positivity
  have ht0 : 0 ≤ C' * (R : ℝ) ^ 2 * boxScale x := by positivity
  have htU : C' * (R : ℝ) ^ 2 * boxScale x ≤ C' * (R : ℝ) ^ 3 * boxScale x := by
    have h1 : (R : ℝ) ^ 2 ≤ (R : ℝ) ^ 3 := pow_le_pow_right₀ hRr (by norm_num)
    have h2 : C' * (R : ℝ) ^ 2 ≤ C' * (R : ℝ) ^ 3 := mul_le_mul_of_nonneg_left h1 hC'0.le
    exact mul_le_mul_of_nonneg_right h2 hδ0
  have hU1 : 2 * (C' * (R : ℝ) ^ 3 * boxScale x) ≤ 1 := by
    have h1 := mul_boxRadius_cube_boxScale_le_one (D := 2 * C') (by positivity) hx1 g11
    rw [← hRR] at h1
    calc 2 * (C' * (R : ℝ) ^ 3 * boxScale x) = 2 * C' * ((R : ℝ) ^ 3 * boxScale x) := by ring
      _ ≤ 1 := h1
  have ht1 : C' * (R : ℝ) ^ 2 * boxScale x ≤ 1 := by linarith
  have hts : C' * (R : ℝ) ^ 2 * boxScale x < (Tb.stepParameters y).threshold := by
    have h1 := mul_boxRadius_cube_boxScale_le_one (D := 2 * C' / (Tb.stepParameters y).threshold) (by positivity) hx1 g13
    rw [← hRR] at h1
    have h2 : 2 * (C' * (R : ℝ) ^ 3 * boxScale x) / (Tb.stepParameters y).threshold ≤ 1 := by
      calc 2 * (C' * (R : ℝ) ^ 3 * boxScale x) / (Tb.stepParameters y).threshold =
            2 * C' / (Tb.stepParameters y).threshold * ((R : ℝ) ^ 3 * boxScale x) := by ring
        _ ≤ 1 := h1
    rw [div_le_one hσ] at h2
    by_cases hz : C' * (R : ℝ) ^ 3 * boxScale x = 0
    · have : C' * (R : ℝ) ^ 2 * boxScale x = 0 := le_antisymm (hz ▸ htU) ht0
      rw [this]
      exact hσ
    · have : 0 < C' * (R : ℝ) ^ 3 * boxScale x := lt_of_le_of_ne hU0 (Ne.symm hz)
      linarith
  have hC₁U : C₁ * (R : ℝ) ^ 3 * boxScale x ≤ C' * (R : ℝ) ^ 3 * boxScale x := by
    have := mul_le_mul_of_nonneg_right hC₁C' hR3
    calc C₁ * (R : ℝ) ^ 3 * boxScale x = C₁ * ((R : ℝ) ^ 3 * boxScale x) := by ring
      _ ≤ C' * ((R : ℝ) ^ 3 * boxScale x) := this
      _ = C' * (R : ℝ) ^ 3 * boxScale x := by ring
  have hC₁t : C₁ * (R : ℝ) ^ 2 * boxScale x ≤ C' * (R : ℝ) ^ 2 * boxScale x := by
    have := mul_le_mul_of_nonneg_right hC₁C' hR2
    calc C₁ * (R : ℝ) ^ 2 * boxScale x = C₁ * ((R : ℝ) ^ 2 * boxScale x) := by ring
      _ ≤ C' * ((R : ℝ) ^ 2 * boxScale x) := this
      _ = C' * (R : ℝ) ^ 2 * boxScale x := by ring
  have herrK : Cm * (3 * (2 / (vt * lengthInSites (Tb.stepParameters y).side K k d)) + Real.exp (-(cm * ((4 * (R + 1) : ℕ) : ℝ)))) +
      (16 * (((4 * (R + 1) : ℕ) : ℝ)) ^ 4) ^ 2 * (Cm * Real.exp (-(cm * ((R : ℝ) - 1)))) ≤
      Cf * ((vt * lengthInSites (Tb.stepParameters y).side K k d)⁻¹ + Real.exp (-(cm / 2 * (R : ℝ)))) := by
    have e1 : 3 * (2 / (vt * lengthInSites (Tb.stepParameters y).side K k d)) = 6 * (vt * lengthInSites (Tb.stepParameters y).side K k d)⁻¹ := by
      ring
    rw [e1]
    exact kernelError_le hcm (by positivity) (by omega) hCf1
  have z1 : Real.exp (-(cf * (R : ℝ))) ≤ (R : ℝ) ^ 8 * boxScale x ^ 3 := by
    have h1 := exp_neg_boxRadius_le hcf g1 g9
    rwa [← hRR] at h1
  have z2 : Real.exp (-(cm * (R : ℝ))) ≤ (R : ℝ) ^ 8 * boxScale x ^ 3 := by
    have h1 := exp_neg_boxRadius_le hcm g1 g7
    rwa [← hRR] at h1
  have herr := responseError_le (Cm := Cm) (cm := cm) (cf := cf) hn1 hRr hδ0 hC'0.le hCf2 z1 z2 (Real.exp_pos (-(cm / 2 * (R : ℝ)))).le
  obtain ⟨x₁, x₂, hf, hh, -⟩ := hpair.mem_class
  have hbf := isBoundedLipschitzBump_of_shaped hd0 hvt0 hf hpair.norm_left
  have hbh := isBoundedLipschitzBump_of_shaped hd0 hvt0 hh hpair.norm_right
  have hflk : ∀ j ≤ k, (Tb.stepParameters y).y₁ ≤ flowCouplings (Tb.stepParameters y) β j := fun j hj => hch.isFlowDatum.le_coupling j (by omega)
  have hnum : IsChainResponseCoeff (Tb.stepParameters y) Kr β k al := by
    rw [hk]
    exact hch.isCoeff
  have hxf : xf ≤ flowCouplings (Tb.stepParameters y) β k := hxk ▸ g5
  have hal : |al k| ≤ 2 := by
    have h1 := abs_le.mp (hNear β k al hflk hnum)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2]
  have hct : C₁ * (R : ℝ) ^ 4 * boxScale x ^ 2 ≤ (C' * (R : ℝ) ^ 2 * boxScale x) ^ 2 := by
    have h1 : C₁ ≤ C' ^ 2 := by nlinarith
    have h2 : 0 ≤ (R : ℝ) ^ 4 * boxScale x ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right h1 h2
    calc C₁ * (R : ℝ) ^ 4 * boxScale x ^ 2 = C₁ * ((R : ℝ) ^ 4 * boxScale x ^ 2) := by ring
      _ ≤ C' ^ 2 * ((R : ℝ) ^ 4 * boxScale x ^ 2) := this
      _ = (C' * (R : ℝ) ^ 2 * boxScale x) ^ 2 := by ring
  obtain ⟨S, hSK, hSrun, hSnum⟩ := hch.scored
  have hF := hFg T S β k (K - 1) (by omega) hSK hSrun hflk hxf (boxSide (Tb.stepParameters y).side K k) hblock
  rw [hSnum] at hF
  have one : ∀ {g : AmbientSpace → ℝ} {cg : AmbientSpace}, IsBoundedLipschitzBump d vt cg g → IsLocalizedNear (Tb.stepParameters y).side K k m R o g →
      ∃ (κ : (Fin 4 → ℤ) → TorusSite (boxSide (Tb.stepParameters y).side K k) → TorusPlaquette (boxSide (Tb.stepParameters y).side K k) →
          TorusPlaquette (boxSide (Tb.stepParameters y).side K k) → ℝ) (κ₀ : (Fin 4 → ℤ) → ℝ),
        IsBoxKernelFamily T β al K k m c Cf (cm / 2)
            (Cf * ((vt * lengthInSites (Tb.stepParameters y).side K k d)⁻¹ + Real.exp (-(cm / 2 * R))))
            (Cf * lengthInSites (Tb.stepParameters y).side K k d ^ 4 * (R : ℝ) ^ 8 * boxScale x ^ 3 + Real.exp (-(cm / 2 * R)))
            (fun v => translateBy (Tb.stepParameters y).side K k v g) κ κ₀ := fun hb hnear =>
    exists_kernelFamily_of_bump hmark hcm hodd hE hN hT hS hW hd0 (by linarith) hvt0 (by omega) c hflk hxk g3 hnum hal hF hchart hR16 hRn hNR hr
      hU0 ht0 hC₁U hU1 hC₁t ht1 hct hts hlip hCmCf (by linarith) (by positivity) herrK herr hb hnear
  obtain ⟨κ, κ₀, h1⟩ := one hbf hnf
  obtain ⟨κ', κ₀', h2⟩ := one hbh hnh
  exact ⟨κ, κ', κ₀, κ₀', h1, h2⟩
end Assembly
theorem boxResponsesQuadratic_holds (hM : curvedFieldResponseStatement) (hF : chainResponseLocalityStatement)
    (hS : unitTorusWeightSizesStatement) (hE : weightExtensionStatement) (hT : WeightsCompatibleAcrossTori)
    (hN : WeightsCloseToBlockMeans) (hW : BlockMeanIsLinearAndLocal) (hL : separationLevelStatement)
    (hC : couplingAtSeparation_tendsto_statement) (hA : ChainResponses.chainResponseCoeffNearOneStatement) : boxResponsesQuadraticStatement := by
  unfold boxResponsesQuadraticStatement HoldsForShapes FreeEnergies.AtResponseParameters
  intro a ha
  obtain ⟨L₁, r₁, c₁, hr₁, H₁⟩ := hM a ha
  obtain ⟨L₂, r₂, c₂, hr₂, H₂⟩ := hF a ha
  obtain ⟨L₃, r₃, c₃, hr₃, H₃⟩ := hL a ha
  obtain ⟨L₄, r₄, c₄, hr₄, H₄⟩ := hC a ha
  obtain ⟨L₅, r₅, c₅, hr₅, H₅⟩ := hA a ha
  refine ⟨max (max (max L₁ L₂) (max L₃ L₄)) L₅, fun c => min (min (min (r₁ c) (r₂ c)) (min (r₃ c) (r₄ c))) (r₅ c),
    max (max (max c₁ c₂) (max c₃ c₄)) c₅, fun c => lt_min (lt_min (lt_min (hr₁ c) (hr₂ c)) (lt_min (hr₃ c) (hr₄ c))) (hr₅ c), ?_⟩
  intro L hodd hLL' Tb hTa hTL hdr hcs hco hrt' hcd' Kr
  have hLL : max (max L₁ L₂) (max L₃ L₄) ≤ L := (le_max_left _ _).trans hLL'
  have l5 : L₅ ≤ L := (le_max_right _ _).trans hLL'
  have hrt := hrt'.trans (min_le_left _ _)
  have t5 : Tb.rt ≤ r₅ Tb.toChainParameters := hrt'.trans (min_le_right _ _)
  have hcd : max (max c₁ c₂) (max c₃ c₄) ≤ Tb.derivBound := (le_max_left _ _).trans hcd'
  have d5 : c₅ ≤ Tb.derivBound := (le_max_right _ _).trans hcd'
  have l1 : L₁ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hLL)
  have l2 : L₂ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hLL)
  have l3 : L₃ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hLL)
  have l4 : L₄ ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hLL)
  have t1 : Tb.rt ≤ r₁ Tb.toChainParameters := hrt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have t2 : Tb.rt ≤ r₂ Tb.toChainParameters := hrt.trans ((min_le_left _ _).trans (min_le_right _ _))
  have t3 : Tb.rt ≤ r₃ Tb.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have t4 : Tb.rt ≤ r₄ Tb.toChainParameters := hrt.trans ((min_le_right _ _).trans (min_le_right _ _))
  have d1 : c₁ ≤ Tb.derivBound := (le_max_left _ _).trans ((le_max_left _ _).trans hcd)
  have d2 : c₂ ≤ Tb.derivBound := (le_max_right _ _).trans ((le_max_left _ _).trans hcd)
  have d3 : c₃ ≤ Tb.derivBound := (le_max_left _ _).trans ((le_max_right _ _).trans hcd)
  have d4 : c₄ ≤ Tb.derivBound := (le_max_right _ _).trans ((le_max_right _ _).trans hcd)
  obtain ⟨y₁, Y₁⟩ := H₁ L hodd l1 Tb hTa hTL hdr hcs hco t1 d1
  obtain ⟨y₂, Y₂⟩ := H₂ L hodd l2 Tb hTa hTL hdr hcs hco t2 d2
  obtain ⟨y₃, Y₃⟩ := H₃ L hodd l3 Tb hTa hTL hdr hcs hco t3 d3
  obtain ⟨y₄, Y₄⟩ := H₄ L hodd l4 Tb hTa hTL hdr hcs hco t4 d4
  obtain ⟨y₅, Y₅⟩ := H₅ L hodd l5 Tb hTa hTL hdr hcs hco t5 d5
  refine ⟨max (max (max y₁ y₂) (max y₃ y₄)) y₅, fun y hy' hstands hKr Xi hXi vt hv0 hv1 C₁ Cj xp => ?_⟩
  have hret := hstands.returns_at
  have hwil : ∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β) := hstands.wilson_expansion
  have hy : max (max y₁ y₂) (max y₃ y₄) ≤ y := (le_max_left _ _).trans hy'
  have P₅ := Y₅ y ((le_max_right _ _).trans hy') hret hwil
  have P₁ := Y₁ y ((le_max_left _ _).trans ((le_max_left _ _).trans hy)) hret hwil
  have P₂ := Y₂ y ((le_max_right _ _).trans ((le_max_left _ _).trans hy)) hret hwil
  have P₃ := Y₃ y ((le_max_left _ _).trans ((le_max_right _ _).trans hy)) hret hwil
  have P₄ := Y₄ y ((le_max_right _ _).trans ((le_max_right _ _).trans hy)) hret hwil
  obtain ⟨Cm, cm, xm, hcm, hmk⟩ := P₁ Kr hKr
  obtain ⟨cf, xf, hcf, hfg⟩ := P₂ Kr hKr
  have hoddT : Odd (Tb.stepParameters y).side := by
    show Odd Tb.side
    rw [hTL]
    exact hodd
  exact exists_kernelFamilies_at_parameters Tb y hdr hret hwil hoddT hE hN hT hS hW Kr hmk hcm hcf hfg hXi (P₃ Xi hXi) (P₄ Xi hXi) (P₅ Kr hKr) hv0 hv1 C₁ Cj xp
end YangMills.Construction.StateLaws
end
