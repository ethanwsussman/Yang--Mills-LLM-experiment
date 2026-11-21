import YangMills.Construction.Lattice.CosetsCoordinatesAndDistancesProof
import YangMills.Construction.Lattice.FirstConsequencesOfTheFiveProperties
import YangMills.Construction.Lattice.LatticesCubesOfAStandardPartitionAndEnlargements
import YangMills.Construction.Lattice.ObservableGeneratingFunctionAndConnectedFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusBound.Consequences
open Topology
theorem side_pos (D : Setup) : 0 < D.side := by apply _root_.YangMills.Construction.TorusBound.Coordinates.setup_side_pos <;> assumption
theorem side_pow_four_pos (D : Setup) : 0 < D.side ^ 4 := pow_pos (side_pos D) 4
theorem disc_mono (D : Setup) {ρ ρ' : ℝ} (h : ρ' ≤ ρ) {n : ℕ} (f : Fin n → D.Torus → ℝ) :
    D.disc ρ' f ⊆ D.disc ρ f :=
  fun _ hz => lt_of_lt_of_le hz h
theorem sources_mono (D : Setup) {ρ ρ' : ℝ} (h : ρ' ≤ ρ) :
    D.sources ρ' ⊆ D.sources ρ := by
  rintro v ⟨n, f, z, hf, hz, rfl⟩
  exact ⟨n, f, z, hf, disc_mono D h f hz, rfl⟩
theorem unitSiteCount_holds
    (hP : CubePartitions.CubePartitionFacts) (D : Setup) :
    UnitSiteCount D := by
  have h := (hP D.toStandingParameters 0 (by simp) 1 (Or.inl rfl)).1.1
  unfold UnitSiteCount
  refine h.trans ?_
  unfold CubePartitions.sitesPerAxis Conventions.StandingParameters.side
    PeriodicLattice.torusSide
  simp
variable {D : Setup} {ρ : ℝ} {hρ : 0 < ρ}
theorem zeroSourceValue_holds (hO : ObservableCumulants.Statement)
    (e : D.RadiusFamily ρ hρ) : ZeroSourceValue e := by
  intro hloc
  have hE : e.totalEnergy (D.zeroSourceAt ρ hρ) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have : (fun X => LocalizedEnergies.EnergyData.EnergyFamily.localEnergy e j X
        (D.zeroSourceAt ρ hρ)) = fun _ => 0 := funext fun X => (hloc j X).2
    rw [this]
    exact finsum_zero
  have hZ : e.normalizedZ (D.zeroSourceAt ρ hρ) =
      Complex.exp (-(e.vacuumTerm : ℂ)) * D.partitionFun (D.zeroSourceAt ρ hρ).1 := by
    unfold Setup.RadiusFamily.normalizedZ
    rw [hE, sub_zero]
  obtain ⟨h0, hpos, -⟩ := (hO D).2.1
  have hval : e.normalizedZ (D.zeroSourceAt ρ hρ) =
      ((Real.exp (-e.vacuumTerm) * PeriodicLattice.partitionFunction D.L D.m D.K D.β : ℝ) :
        ℂ) := by
    rw [hZ]
    have h0' : D.partitionFun (D.zeroSourceAt ρ hρ).1 =
        (PeriodicLattice.partitionFunction D.L D.m D.K D.β : ℂ) := h0
    rw [h0']
    push_cast
    rfl
  refine ⟨hE, hZ, ?_, ?_⟩
  · rw [hval, Complex.ofReal_im]
  · rw [hval, Complex.ofReal_re]
    exact mul_pos (Real.exp_pos _) hpos
theorem constantsSumNonneg_holds (e : D.RadiusFamily ρ hρ) (A B : ℝ) :
    ConstantsSumNonneg e A B := by
  intro hup hlow
  have h1 : (e.normalizedZ (D.zeroSourceAt ρ hρ)).re ≤
      ‖e.normalizedZ (D.zeroSourceAt ρ hρ)‖ := Complex.re_le_norm _
  have h2 := hlow.2.trans (h1.trans (hup _))
  have h3 := Real.exp_le_exp.mp h2
  have hs := side_pow_four_pos D
  by_contra hneg
  have : (A + B) * D.side ^ 4 < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) hs
  nlinarith
theorem constantsMonotone_holds (e : D.RadiusFamily ρ hρ) (A B : ℝ) :
    ConstantsMonotone e A B := by
  have hs := side_pow_four_pos D
  refine ⟨fun hup A' hA' w => (hup w).trans (Real.exp_le_exp.mpr ?_),
    fun hlow B' hB' => ⟨hlow.1, (Real.exp_le_exp.mpr ?_).trans hlow.2⟩⟩
  · exact mul_le_mul_of_nonneg_right hA' hs.le
  · exact mul_le_mul_of_nonneg_right (neg_le_neg hB') hs.le
theorem mul_le_plusPart_mul (t V S : ℝ) (hV : 0 ≤ V) (hVS : V ≤ S) :
    t * V ≤ plusPart t * S := by
  have h1 : t ≤ plusPart t := le_max_left _ _
  have h2 : 0 ≤ plusPart t := le_max_right _ _
  calc t * V ≤ plusPart t * V := mul_le_mul_of_nonneg_right h1 hV
    _ ≤ plusPart t * S := mul_le_mul_of_nonneg_left hVS h2
theorem volumeBounds_holds (e : D.RadiusFamily ρ hρ) (A B : ℝ) :
    VolumeBounds e A B := by
  intro V hV hVS
  refine ⟨fun hb w => (hb w).trans (Real.exp_le_exp.mpr
      (mul_le_plusPart_mul A V _ hV hVS)),
    fun him hre => ⟨him, (Real.exp_le_exp.mpr ?_).trans hre⟩⟩
  have := mul_le_plusPart_mul B V _ hV hVS
  linarith
theorem restrict_analytic
    (hdisc : SourceDiskAndClass.Statement) (e : D.RadiusFamily ρ hρ) {ρ' : ℝ} (hρ' : 0 < ρ')
    (hle : ρ' ≤ ρ) (hsub : D.sources ρ' ⊆ D.sources ρ) (hA : e.Analytic) :
    (e.restrict hρ' hsub).Analytic := by
  intro j X n h hh
  have hopen : IsOpen (D.disc ρ' h) := (hdisc D h ρ' hh hρ').2.2.1
  have hagree : ∀ ζ ∈ D.disc ρ' h,
      LocalizedEnergies.EnergyData.EnergyFamily.localEnergyAlong (e.restrict hρ' hsub) j X h hh ζ =
        LocalizedEnergies.EnergyData.EnergyFamily.localEnergyAlong e j X h hh ζ := by
    intro ζ hζ
    have hζ' : ζ ∈ D.disc ρ h := disc_mono D hle h hζ
    unfold LocalizedEnergies.EnergyData.EnergyFamily.localEnergyAlong
    rw [dif_pos hζ, dif_pos hζ']
    rfl
  obtain ⟨-, hcont, hdiff⟩ := hA j X n h hh
  refine ⟨hopen, ?_, ?_⟩
  · refine (hcont.mono (disc_mono D hle h)).congr fun ζ hζ => ?_
    funext _
    exact hagree ζ hζ
  · intro a ha i
    have hline : Continuous fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector i := by
      fun_prop
    have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ),
        a + ζ • Coordinates.ComplexCoordinates.stdBasisVector i ∈ D.disc ρ' h := by
      refine hline.continuousAt.eventually_mem (hopen.mem_nhds ?_)
      simpa using ha
    filter_upwards [hdiff a (disc_mono D hle h ha) i, hnear.eventually_nhds] with ζ hζ hnearζ
    refine hζ.congr_of_eventuallyEq ?_
    filter_upwards [hnearζ] with ξ hξ
    funext _
    exact hagree _ hξ
theorem restrictionInherits_holds (hdisc : SourceDiskAndClass.Statement)
    (e : D.RadiusFamily ρ hρ) : RestrictionInherits e := by
  intro ρ' hρ' hle
  refine ⟨sources_mono D hle, ?_, restrict_analytic hdisc e hρ' hle _, ?_, ?_, ?_⟩
  · intro hloc j X
    exact ⟨fun v v' hv => (hloc j X).1 _ _ hv, (hloc j X).2⟩
  · intro C κ hB
    exact ⟨hB.1, hB.2.1, fun j X v => hB.2.2 j X _⟩
  · intro A hup w
    exact hup _
  · intro B hlow
    exact hlow
theorem allHold_proof (hP : CubePartitions.CubePartitionFacts)
    (hdisc : SourceDiskAndClass.Statement)
    (hO : ObservableCumulants.Statement) : AllHold := by
  intro D ρ hρ e A B
  exact ⟨unitSiteCount_holds hP D, zeroSourceValue_holds hO e, constantsSumNonneg_holds e A B,
    restrictionInherits_holds hdisc e, constantsMonotone_holds e A B, volumeBounds_holds e A B⟩
end YangMills.Construction.TorusBound.Consequences
end
