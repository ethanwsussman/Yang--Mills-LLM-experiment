import YangMills.Construction.Towers.IteratesOfTheLinearMapsAsMeansOverBlocks
import YangMills.Construction.Towers.IteratesOfTheStraightAverageKeepTheForms
import YangMills.Construction.Towers.MeansOfPlaneWavesAlongStraightPaths
import YangMills.Construction.Towers.PlaneWavesUnderTheDilationOfOneStep
import YangMills.Construction.Towers.PlaneWavesUnderTheMapOfOneStep
import YangMills.Construction.Towers.ResponseOfAPlaneWaveOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.StepImageOfFourierModes
open YangMills.Construction.Tower
open YangMills.Construction.Tower.PlaneWaves (freqBox)
open YangMills.Construction.Tower.CriticalBranchResponse (meshScaledResponse)
open YangMills.Construction.PeriodicOperators (toComplexVec dualLattice)
open YangMills.Construction.PeriodicOperators.Tempered YangMills.Construction.PeriodicOperators.Tempered.OneStep
open YangMills.Construction.Tower.StraightPathMeans (pathAverage)
open YangMills.Construction.Tower.PeriodicResponseOfFourierMode (complexPeriodicResponse)
open Classical in
theorem sum_residueBox_fibres {L : ℕ} (hL : 0 < L) (F : Finset (Fin 4 → ℤ))
    (g : (Fin 4 → ℤ) → Matrices.ComplexMatrix2) :
    ∑ r ∈ residueBox L, ∑ k ∈ F.filter (fun k => ∀ ν, (L : ℤ) ∣ k ν - r ν), g k = ∑ k ∈ F, g k := by
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  have key : ∀ (r k : Fin 4 → ℤ), r ∈ residueBox L ∧ k ∈ F.filter (fun k => ∀ ν, (L : ℤ) ∣ k ν - r ν) ↔
      r ∈ ({fun ν => k ν % (L : ℤ)} : Finset (Fin 4 → ℤ)) ∧ k ∈ F := by
    intro r k
    simp only [residueBox, Fintype.mem_piFinset, Finset.mem_Ico, Finset.mem_filter,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hr, hk, hd⟩
      refine ⟨funext fun ν => ?_, hk⟩
      have h1 : k ν % (L : ℤ) = r ν % (L : ℤ) :=
        Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd (hd ν))
      rw [h1, Int.emod_eq_of_lt (hr ν).1 (hr ν).2]
    · rintro ⟨rfl, hk⟩
      exact ⟨fun ν => ⟨Int.emod_nonneg _ hLz.ne', Int.emod_lt_of_pos _ hLz⟩, hk,
        fun ν => Int.dvd_of_emod_eq_zero (by
          rw [Int.sub_emod, Int.emod_emod_of_dvd _ dvd_rfl, sub_self, Int.zero_emod])⟩
  have := Finset.sum_comm' (s := residueBox L)
    (t := fun r => F.filter (fun k => ∀ ν, (L : ℤ) ∣ k ν - r ν)) (t' := F)
    (s' := fun k => ({fun ν => k ν % (L : ℤ)} : Finset (Fin 4 → ℤ))) (f := fun _ k => g k) key
  simpa using this
theorem finestMesh_mul_pow {L : ℕ} (hL : 0 < L) (i : ℕ) :
    ((finestMesh L (i + 1) : ℝ) : ℂ) * (L : ℂ) ^ i = (L : ℂ)⁻¹ := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  simp only [finestMesh, meshAt]
  push_cast
  rw [show ((0 : ℤ) - ((i : ℤ) + 1)) = -((i + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  rw [pow_succ]
  field_simp
theorem toComplexVec_shifted (p : InfiniteLattice.AmbientSpace) (k : Fin 4 → ℤ) :
    toComplexVec (fun ν => p ν + 2 * Real.pi * (k ν : ℝ)) =
      Tower.PlaneWaves.shiftedFreq (toComplexVec p) k := by
  funext ν
  simp [toComplexVec, Tower.PlaneWaves.shiftedFreq]
theorem pushforward_forwardFrom {L : ℕ} (hL : 0 < L) (hst : Conventions.IsAdmissibleBlockingFactor L)
    {n i : ℕ} (hn : 0 < n)
    (hM : Tower.StraightPathMeans.PlaneWaveMeans)
    (hD : Tower.StepScalingOfFourierModes.Claim)
    (hI : Tower.IteratesAsCubeAverages)
    {p : InfiniteLattice.AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ n)) (a : Fin 3) (μ : Fin 4)
    (hR : ∀ (ρ : Fin 4) (x : Vertex L n (i + 1) 0),
      complexPeriodicResponse L n i (fourierModeForm L n a p μ) (PeriodicLattice.Bond.forwardFrom x ρ) =
        ∑ k ∈ freqBox L (i + 1),
          (phase (L := L) (n := n) (fun ν => p ν + 2 * Real.pi * (k ν : ℝ))
              (x : PeriodicLattice.FourTorus L n) *
            responseCoeff L (i + 1) (toComplexVec p) ρ μ k) • Matrices.ComplexMatrix2.pauliFamily a)
    (y : Vertex L n (i + 1) i) (ρ : Fin 4) :
    complexStepPushforward hL n i (fourierModeForm L n a p μ)
        (stepEdgeEquiv hL n i (PeriodicLattice.Bond.forwardFrom y ρ)) =
      ((L : ℂ)⁻¹ • ∑ r ∈ residueBox L, ∑ σ,
        stepEntry L i r (toComplexVec p) σ μ • fourierModeForm L (n + 1) a (rescaledMomentum L p r) σ)
        (stepEdgeEquiv hL n i (PeriodicLattice.Bond.forwardFrom y ρ)) := by
  classical
  obtain ⟨-, -, hmom, hwave, hcong⟩ := hD L hL hst n i hn
  set E := fourierModeForm L n a p μ with hE
  set uR := meshScaledResponse L n (i + 1) (topLevelForm L n (i + 1) (realComponent E)) with huR
  set uI := meshScaledResponse L n (i + 1) (topLevelForm L n (i + 1) (imagComponent E)) with huI
  set e := PeriodicLattice.Bond.forwardFrom y ρ with he
  set q : (Fin 4 → ℤ) → InfiniteLattice.AmbientSpace := fun k ν => p ν + 2 * Real.pi * (k ν : ℝ) with hq
  set C : (Fin 4 → ℤ) → ℂ := fun k => responseCoeff L (i + 1) (toComplexVec p) ρ μ k with hC
  set η : ℂ := ((finestMesh L (i + 1) : ℝ) : ℂ) with hη
  have hmean := (hI L hst n (i + 1) i hn (Nat.le_succ i)).1
  have hval : ∀ x : Vertex L n (i + 1) 0,
      (uR : Edge L n (i + 1) 0 → Matrices.ComplexMatrix2) (PeriodicLattice.Bond.forwardFrom x ρ) +
          Complex.I • (uI : Edge L n (i + 1) 0 → Matrices.ComplexMatrix2)
            (PeriodicLattice.Bond.forwardFrom x ρ) =
        ∑ k ∈ freqBox L (i + 1), phase (L := L) (n := n) (q k)
          (x : PeriodicLattice.FourTorus L n) • ((η * C k) • Matrices.ComplexMatrix2.pauliFamily a) := by
    intro x
    have h := hR ρ x
    simp only [complexPeriodicResponse, Pi.add_apply, Pi.smul_apply] at h
    have : (uR : Edge L n (i + 1) 0 → Matrices.ComplexMatrix2) (PeriodicLattice.Bond.forwardFrom x ρ) +
          Complex.I • (uI : Edge L n (i + 1) 0 → Matrices.ComplexMatrix2)
            (PeriodicLattice.Bond.forwardFrom x ρ) =
        η • ((CriticalBranchResponse.periodicResponse L n (i + 1)
            (topLevelForm L n (i + 1) (realComponent E)) : Edge L n (i + 1) 0 → Matrices.ComplexMatrix2)
              (PeriodicLattice.Bond.forwardFrom x ρ) +
          Complex.I • (CriticalBranchResponse.periodicResponse L n (i + 1)
            (topLevelForm L n (i + 1) (imagComponent E)) : Edge L n (i + 1) 0 → Matrices.ComplexMatrix2)
              (PeriodicLattice.Bond.forwardFrom x ρ)) := by
      simp only [huR, huI, meshScaledResponse, Submodule.coe_smul, Pi.smul_apply, smul_add, hη]
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_comm Complex.I]
    rw [this, h, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [smul_smul]
    congr 1
    ring
  have hmeans := hM L hst n i hn y ρ (freqBox L (i + 1)) q
    (fun k => (η * C k) • Matrices.ComplexMatrix2.pauliFamily a) uR uI (fun k _ => hmom p hp k) hval
  have hleft : complexStepPushforward hL n i E (stepEdgeEquiv hL n i e) =
      pathAverage L n i uR y ρ + Complex.I • pathAverage L n i uI y ρ := by
    simp only [complexStepPushforward, stepPushforward, Pi.add_apply, Pi.smul_apply, transportTotal,
      Function.comp_apply, Equiv.symm_apply_apply]
    rw [hmean uR uR.2 e, hmean uI uI.2 e]
    rfl
  rw [hleft, hmeans]
  simp only [Pi.smul_apply, Finset.sum_apply]
  have hin : ∀ r : Fin 4 → ℤ, ∑ σ, stepEntry L i r (toComplexVec p) σ μ •
        fourierModeForm L (n + 1) a (rescaledMomentum L p r) σ (stepEdgeEquiv hL n i e) =
      ∑ k ∈ (freqBox L (i + 1)).filter (fun k => ∀ ν, (L : ℤ) ∣ k ν - r ν),
        (stepMean L i ρ (toComplexVec (q k)) * C k *
          phase (L := L) (n := n) (q k) (y : PeriodicLattice.FourTorus L n)) •
            Matrices.ComplexMatrix2.pauliFamily a := by
    intro r
    simp only [he, hwave p hp r y ρ _ a, smul_ite, smul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [stepEntry, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [toComplexVec_shifted, ← hcong p hp k r y (Finset.mem_filter.1 hk).2, smul_smul]
  simp only [hin]
  rw [sum_residueBox_fibres hL, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [smul_smul]
  congr 1
  rw [← finestMesh_mul_pow hL i, ← hη]
  ring
theorem imageExpansion_holds (hR : Tower.PeriodicResponseOfFourierMode.Claim)
    (hM : Tower.StraightPathMeans.PlaneWaveMeans)
    (hD : Tower.StepScalingOfFourierModes.Claim)
    (hF : Tower.CrossingSmoothingIterMapsForms)
    (hI : Tower.IteratesAsCubeAverages) : ImageExpansion := by
  intro L hL hst i
  obtain ⟨s₀, hs₀, h⟩ := hR L hst i
  refine ⟨s₀, hs₀, fun s hs hle n hn hside p hp a μ => ?_⟩
  have hRn := h s hs hle n hn hside p hp a μ
  obtain ⟨hrev, hwrev, -, -, -⟩ := hD L hL hst n i hn
  have hfwd := pushforward_forwardFrom hL hst hn hM hD hI hp a μ hRn
  funext b
  obtain ⟨c, rfl⟩ := (stepEdgeEquiv hL n i).surjective b
  obtain ⟨ρ, hc | hc⟩ := c.isNeighbour
  · have : c = PeriodicLattice.Bond.forwardFrom c.source ρ := by
      cases c with
      | mk t h ad =>
        simp only [PeriodicLattice.Bond.forwardFrom, PeriodicLattice.Bond.mk.injEq, true_and]
        exact sub_eq_iff_eq_add'.1 hc
    rw [this]
    exact hfwd _ ρ
  · have hcr : c.opposite = PeriodicLattice.Bond.forwardFrom c.target ρ := by
      cases c with
      | mk t h ad =>
        simp only [PeriodicLattice.Bond.forwardFrom, PeriodicLattice.Bond.opposite,
          PeriodicLattice.Bond.mk.injEq, true_and]
        rw [← sub_eq_iff_eq_add', ← neg_sub, hc, neg_neg]
    have hrr : c = (PeriodicLattice.Bond.forwardFrom c.target ρ).opposite := by rw [← hcr]; rfl
    rw [hrr, hrev]
    have hleft : ∀ d : Edge L n (i + 1) i, complexStepPushforward hL n i (fourierModeForm L n a p μ)
        (stepEdgeEquiv hL n i d).opposite = -complexStepPushforward hL n i (fourierModeForm L n a p μ)
          (stepEdgeEquiv hL n i d) := by
      intro d
      rw [← hrev]
      simp only [complexStepPushforward, stepPushforward, Pi.add_apply, Pi.smul_apply, transportTotal,
        Function.comp_apply, Equiv.symm_apply_apply]
      rw [(hF L hst n i hn _ (Submodule.coe_mem _)).2 d, (hF L hst n i hn _ (Submodule.coe_mem _)).2 d]
      simp [smul_neg, neg_add]
      try abel
    rw [hleft, hfwd]
    simp only [Pi.smul_apply, Finset.sum_apply, hwrev, smul_neg, Finset.sum_neg_distrib]
end YangMills.Construction.Tower.StepImageOfFourierModes
end
