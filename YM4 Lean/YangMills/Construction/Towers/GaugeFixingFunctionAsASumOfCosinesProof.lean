import YangMills.Construction.OneLoop.PauliMatrixRelations
import YangMills.Construction.Towers.DerivativeOfTheContourLogarithmAlongCurvesProof
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.Tower
def contourLog (L n k i : ℕ) (V : Edge L n k i → Matrices.ComplexMatrix2) :
    FineOnlyVertex L n k i → Matrices.ComplexMatrix2 :=
  fun x => Complex.I⁻¹ •
    Matrices.ComplexMatrix2.logSeries (PeriodicLattice.meanContourHolonomy V (cubeCentre x) x.1)
def AxialFunctionCosineSum : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    Finite (FineOnlyVertex L n k i) ∧
      EventuallyNearIdentity (fieldSpace L n k i) fun V =>
        V ∈ axialFunctionDomain L n k i ∧
          (∀ x, contourLog L n k i V x ∈ Matrices.ComplexMatrix2.hermitianTraceless) ∧
          axialFunction L n k i V =
            ∑ᶠ x, (1 - Real.cos (Matrices.ComplexMatrix2.operatorNorm (contourLog L n k i V x))) ∧
          0 ≤ axialFunction L n k i V ∧
          (axialFunction L n k i V = 0 ↔ IsAxialGaugeAt L n k i V)
end YangMills.Construction.Tower
end

open Filter Set
open scoped Topology Matrix.Norms.L2Operator
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.Tower
namespace AxialCosine
variable {L n k i : ℕ}
private theorem traceDeficit_of_norm_sub_one_lt (hExpLog : ComplexMatrix2.ExpLogEstimates)
    (hPauli : OneLoop.PauliMatrixRelations) {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) (hnear : ComplexMatrix2.operatorNorm (g - 1) < 1) :
    Complex.I⁻¹ • ComplexMatrix2.logSeries g ∈ ComplexMatrix2.hermitianTraceless ∧
      PeriodicLattice.traceDeficit g =
        1 - Real.cos (ComplexMatrix2.operatorNorm (Complex.I⁻¹ • ComplexMatrix2.logSeries g)) ∧
      (PeriodicLattice.traceDeficit g = 0 → g = 1) := by
  obtain ⟨-, -, -, -, -, -, -, hU, -, -⟩ := hExpLog
  obtain ⟨-, -, -, -, -, -, -, -, hcos, -, -⟩ := hPauli
  have hmem := Matrix.mem_specialUnitaryGroup_iff.mp hg
  obtain ⟨X, -, hlog, hnorm, hexp, -, hdet⟩ := hU g hmem.1 hnear
  obtain ⟨-, hX, -, -⟩ := hdet hmem.2
  have hXeq : Complex.I⁻¹ • ComplexMatrix2.logSeries g = X := by
    rw [hlog, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  have hdef : PeriodicLattice.traceDeficit g = 1 - Real.cos (ComplexMatrix2.operatorNorm X) := by
    have hre := congrArg Complex.re (hcos X hX)
    rw [hexp] at hre
    rw [Complex.ofReal_re] at hre
    rw [← hre]
    simp [PeriodicLattice.traceDeficit, ComplexMatrix2.halfTrace]
  rw [hXeq]
  refine ⟨hX, hdef, fun hzero => ?_⟩
  have hc : Real.cos (ComplexMatrix2.operatorNorm X) = 1 := by linarith
  have hnn : 0 ≤ ComplexMatrix2.operatorNorm X := norm_nonneg _
  have hz : ComplexMatrix2.operatorNorm X = 0 :=
    (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])).mp hc
  have hX0 : X = 0 := norm_eq_zero.mp hz
  rw [← hexp, hX0]
  simp [ComplexMatrix2.matExp]
private theorem cubeCentre_spec (hpart : BlocksPartitionFiner L n k (i + 1))
    (v : FineOnlyVertex L n k i) :
    v.1 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) (cubeCentre v) ∧
      (v.1 : PeriodicLattice.FourTorus L n) ≠ cubeCentre v := by
  obtain ⟨c, ⟨hc, hne⟩, -⟩ := hpart.2.2 v.1 v.2
  exact Classical.epsilon_spec (p := fun c : Vertex L n k (i + 1) =>
    v.1 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) c ∧
      (v.1 : PeriodicLattice.FourTorus L n) ≠ c) ⟨c, hc, hne⟩
abbrev _root_.YangMills.SharedProofs.p27590 := @cubeCentre_spec
private theorem not_mem_coarse_of_mem_block (hpart : BlocksPartitionFiner L n k (i + 1))
    {c : Vertex L n k (i + 1)} {w : Vertex L n k i}
    (hw : w ∈ PeriodicLattice.blockSitesExceptCenter k i c) :
    (w : PeriodicLattice.FourTorus L n) ∉
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (i + 1)) := by
  intro hcoarse
  have hboth : (w : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock c ∩
      (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (i + 1)) :
        Set (PeriodicLattice.FourTorus L n)) := ⟨hw.1, hcoarse⟩
  rw [hpart.1 c] at hboth
  exact hw.2 hboth
abbrev _root_.YangMills.SharedProofs.p129669 := @not_mem_coarse_of_mem_block
private theorem cubeCentre_eq_of_mem (hpart : BlocksPartitionFiner L n k (i + 1))
    {c : Vertex L n k (i + 1)} (v : FineOnlyVertex L n k i)
    (hv : v.1 ∈ PeriodicLattice.blockSitesExceptCenter k i c) : cubeCentre v = c := by
  obtain ⟨u, -, huniq⟩ := hpart.2.2 v.1 v.2
  have hs := cubeCentre_spec hpart v
  exact (huniq _ ⟨hs.1, hs.2⟩).trans (huniq _ ⟨hv.1, hv.2⟩).symm
private theorem axialFunction_eq_finsum (hpart : BlocksPartitionFiner L n k (i + 1))
    [Finite (Vertex L n k (i + 1))] [Finite (Vertex L n k i)] (U : Edge L n k i → ComplexMatrix2) :
    axialFunction L n k i U = ∑ᶠ v : FineOnlyVertex L n k i,
      PeriodicLattice.traceDeficit
        (PeriodicLattice.meanContourHolonomy U (cubeCentre v) v.1) := by
  classical
  have := Fintype.ofFinite (Vertex L n k (i + 1))
  have := Fintype.ofFinite (FineOnlyVertex L n k i)
  have hfibre : ∀ c : Vertex L n k (i + 1), PeriodicLattice.blockSitesExceptCenter k i c =
      Subtype.val '' {v : FineOnlyVertex L n k i | cubeCentre v = c} := by
    intro c
    ext w
    constructor
    · intro hw
      exact ⟨⟨w, not_mem_coarse_of_mem_block hpart hw⟩,
        cubeCentre_eq_of_mem hpart ⟨w, not_mem_coarse_of_mem_block hpart hw⟩ hw, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      have hs := cubeCentre_spec hpart v
      have hv' : cubeCentre v = c := hv
      rw [hv'] at hs
      exact ⟨hs.1, hs.2⟩
  have hinner : ∀ c : Vertex L n k (i + 1),
      ∑ᶠ w ∈ PeriodicLattice.blockSitesExceptCenter k i c,
        PeriodicLattice.traceDeficit (PeriodicLattice.meanContourHolonomy U c w) =
      ∑ v ∈ Finset.univ.filter fun v : FineOnlyVertex L n k i => cubeCentre v = c,
        PeriodicLattice.traceDeficit
          (PeriodicLattice.meanContourHolonomy U (cubeCentre v) v.1) := by
    intro c
    have hset : {v : FineOnlyVertex L n k i | cubeCentre v = c} =
        ↑(Finset.univ.filter fun v : FineOnlyVertex L n k i => cubeCentre v = c) := by
      ext v
      simp
    rw [hfibre c, finsum_mem_image Subtype.val_injective.injOn, hset, finsum_mem_coe_finset]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [(Finset.mem_filter.mp hv).2]
  unfold axialFunction PeriodicLattice.axialGaugeFunction
  simp only [finsum_mem_univ, hinner]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  exact Finset.sum_fiberwise _ _ _
private theorem expCurve_zero_zero {U : Edge L n k i → ComplexMatrix2} (hU : U ∈ fieldSpace L n k i) :
    ContourLogarithms.expCurve U 0 0 = U := by
  funext e
  have hopp : e.opposite.opposite = e := PeriodicLattice.Bond.ext rfl rfl
  have hexp0 : ComplexMatrix2.matExp (0 : ComplexMatrix2) = 1 := by simp [ComplexMatrix2.matExp]
  by_cases he : e.IsPositivelyOriented
  · simp [ContourLogarithms.expCurve, PeriodicLattice.expTwist, he]
  · have hinv := hU.2 e.opposite (mem_univ _)
    simp only [ContourLogarithms.expCurve, PeriodicLattice.expTwist, if_neg he]
    simp only [Complex.ofReal_zero, Pi.zero_apply, smul_zero, hexp0, one_mul]
    rw [← hinv, hopp]
private theorem meanContourHolonomy_mem {U : Edge L n k i → ComplexMatrix2} {c : Vertex L n k (i + 1)}
    {w : Vertex L n k i} (h : PeriodicLattice.HasContourMean U c w) :
    PeriodicLattice.meanContourHolonomy U c w ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.SharedProofs.p41932 <;> assumption
end AxialCosine
open AxialCosine in
theorem axialFunctionCosineSum_of
    (hLog : ContourLogarithms.ContourLogDifferentiable)
    (hCubes : BlockStructure)
    (hExpLog : ComplexMatrix2.ExpLogEstimates)
    (hPauli : OneLoop.PauliMatrixRelations)
    (hLat : QuotientLattices.TorusAndSpaceLatticeProperties) :
    AxialFunctionCosineSum := by
  intro L n k i hL hn hi
  have hfin : ∀ r, r ≤ k → Finite (Vertex L n k r) := by
    intro r hr
    obtain ⟨-, hq, -⟩ := hLat L hL n r k hn hr
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hf, -, -⟩ := hq
    exact hf
  have : Finite (Vertex L n k (i + 1)) := hfin (i + 1) hi
  have : Finite (Vertex L n k i) := hfin i hi.le
  have hpart : BlocksPartitionFiner L n k (i + 1) :=
    ((hCubes L k (i + 1) hL (by omega) (by omega) (by omega)).1 n hn).2.1
  refine ⟨inferInstance, ?_⟩
  have hev := (hLog L n k hL hn i hi).2
  unfold EventuallyNearIdentity at hev ⊢
  refine (hev.and self_mem_nhdsWithin).mono ?_
  rintro U ⟨hU, hfield⟩
  have hnear : ∀ (c : Vertex L n k (i + 1)) (w : Vertex L n k i),
      w ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) c →
      PeriodicLattice.HasContourMean U c w ∧
        ComplexMatrix2.operatorNorm (PeriodicLattice.meanContourHolonomy U c w - 1) < 1 := by
    intro c w hw
    have h0 := (hU (c, w) hw 0 (edgeFormSpace L n k i).zero_mem).1.self_of_nhds
    rwa [expCurve_zero_zero hfield] at h0
  have hfacts : ∀ v : FineOnlyVertex L n k i,
      contourLog L n k i U v ∈ ComplexMatrix2.hermitianTraceless ∧
        PeriodicLattice.traceDeficit
            (PeriodicLattice.meanContourHolonomy U (cubeCentre v) v.1) =
          1 - Real.cos (ComplexMatrix2.operatorNorm (contourLog L n k i U v)) ∧
        (PeriodicLattice.traceDeficit
            (PeriodicLattice.meanContourHolonomy U (cubeCentre v) v.1) = 0 →
          PeriodicLattice.meanContourHolonomy U (cubeCentre v) v.1 = 1) := by
    intro v
    have hv := hnear _ _ (cubeCentre_spec hpart v).1
    exact traceDeficit_of_norm_sub_one_lt hExpLog hPauli (meanContourHolonomy_mem hv.1) hv.2
  have hsum : axialFunction L n k i U =
      ∑ᶠ v, (1 - Real.cos (ComplexMatrix2.operatorNorm (contourLog L n k i U v))) := by
    rw [axialFunction_eq_finsum hpart]
    exact finsum_congr fun v => (hfacts v).2.1
  have hterm : ∀ v : FineOnlyVertex L n k i,
      0 ≤ 1 - Real.cos (ComplexMatrix2.operatorNorm (contourLog L n k i U v)) :=
    fun v => sub_nonneg.mpr (Real.cos_le_one _)
  refine ⟨⟨hfield, fun c _ w hw => (hnear c w hw.1).1⟩, fun v => (hfacts v).1, hsum,
    hsum ▸ finsum_nonneg hterm, ?_, ?_⟩
  · intro h0
    classical
    have := Fintype.ofFinite (FineOnlyVertex L n k i)
    rw [hsum, finsum_eq_sum_of_fintype,
      Finset.sum_eq_zero_iff_of_nonneg fun v _ => hterm v] at h0
    refine ⟨⟨hi, ⟨fun e _ => hfield.1 e (mem_univ _), fun e _ => hfield.2 e (mem_univ _)⟩,
      fun c _ w hw => (hnear c w hw).1⟩, fun c _ w hw hne => ?_⟩
    have hw' : w ∈ PeriodicLattice.blockSitesExceptCenter k i c := ⟨hw, hne⟩
    have hoff := not_mem_coarse_of_mem_block hpart hw'
    have hcen := cubeCentre_eq_of_mem hpart ⟨w, hoff⟩ hw'
    have hX := (hfacts ⟨w, hoff⟩).2
    have hzero := h0 ⟨w, hoff⟩ (Finset.mem_univ _)
    have hone := hX.2 (hX.1.trans hzero)
    rwa [hcen] at hone
  · intro htriv
    have hone : PeriodicLattice.traceDeficit (1 : ComplexMatrix2) = 0 := by
      norm_num [PeriodicLattice.traceDeficit, ComplexMatrix2.fullTrace, Matrix.trace_one]
    rw [axialFunction_eq_finsum hpart]
    refine finsum_eq_zero_of_forall_eq_zero fun v => ?_
    have hs := cubeCentre_spec hpart v
    rw [htriv.2 _ (mem_univ _) v.1 hs.1 hs.2, hone]
end YangMills.Construction.Tower
end
