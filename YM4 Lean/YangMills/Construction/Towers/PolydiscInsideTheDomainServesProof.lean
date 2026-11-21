import YangMills.Construction.Lattice.BondsPathsAndAveragesOfADoubleBlock
import YangMills.Construction.Towers.ConfigurationsOnFiniteBondSets
import YangMills.Construction.Towers.PolydiscInsideTheDomainServes
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
open Matrices Coordinates BondSetFields
private theorem isHolomorphicIn_mono_congr {N N' : ℕ} {U U' : Set (ComplexCoordinates N)}
    {f g : ComplexCoordinates N → ComplexCoordinates N'} (hU' : IsOpen U') (hUU : U' ⊆ U)
    (hfg : EqOn g f U') (hf : ComplexCoordinates.IsHolomorphicIn U f) :
    ComplexCoordinates.IsHolomorphicIn U' g := by
  refine ⟨hU', (hf.2.1.mono hUU).congr hfg, fun a ha j => ?_⟩
  have hline : Continuous fun z : ℂ => a + z • ComplexCoordinates.stdBasisVector j :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), a + z • ComplexCoordinates.stdBasisVector j ∈ U' :=
    hline.continuousAt.eventually_mem (by simpa using hU'.mem_nhds ha)
  filter_upwards [hf.2.2 a (hUU ha) j, eventually_eventually_nhds.2 hnear] with z hdiff hev
  exact hdiff.congr_of_eventuallyEq (hev.mono fun w hw => hfg hw)
private theorem continuous_expChart_tracelessTuple {N : ℕ}
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (X : Fin N → ComplexMatrix2) :
    Continuous fun w : ComplexCoordinates (N * 3) =>
      ComplexCoordinates.expChart X (ComplexCoordinates.tracelessTuple β w) := by
  refine continuous_pi fun r => ?_
  have hlin : Continuous fun w : ComplexCoordinates (N * 3) =>
      ComplexCoordinates.tracelessTuple β w r :=
    continuous_finsetSum _ fun s _ => (continuous_apply _).smul continuous_const
  let +nondep : NormedAlgebra ℚ ComplexMatrix2 := .restrictScalars ℚ ℂ ComplexMatrix2
  exact (NormedSpace.exp_continuous.comp hlin).mul continuous_const
private theorem expChart_tracelessTuple_zero {N : ℕ}
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (X : Fin N → ComplexMatrix2) :
    ComplexCoordinates.expChart X (ComplexCoordinates.tracelessTuple β 0) = X := by
  funext r
  simp [ComplexCoordinates.expChart, ComplexCoordinates.tracelessTuple, ComplexMatrix2.matExp]
section Restriction
variable {L m : ℕ} {i : ℤ}
private theorem isHolomorphicOnFields_mono_congr {B : Set (PeriodicLattice.Bond L m i)}
    {D D' : Set (PeriodicLattice.Bond L m i → ComplexMatrix2)}
    {F F' : (PeriodicLattice.Bond L m i → ComplexMatrix2) → ComplexMatrix2} (hDD : D' ⊆ D)
    (hopen : ComplexMatrix2.IsRelativelyOpen
      (ComplexMatrix2.complexifiedProduct fun _ : PeriodicLattice.PositiveBondOf B =>
        ComplexMatrix2.FactorKind.group)
      (PeriodicLattice.restrictToPositive B '' D'))
    (hFF : ∀ v ∈ PeriodicLattice.restrictToPositive B '' D',
      F' (PeriodicLattice.extendFromPositive B v) =
        F (PeriodicLattice.extendFromPositive B v))
    (hF : PeriodicLattice.IsHolomorphicOnFields B D F) :
    PeriodicLattice.IsHolomorphicOnFields B D' F' := by
  have himg : PeriodicLattice.restrictToPositive B '' D' ⊆
      PeriodicLattice.restrictToPositive B '' D :=
    image_mono hDD
  obtain ⟨⟨inst, -, hmaps, hloc⟩, hchart⟩ := hF
  refine ⟨⟨inst, hopen, ?_, ?_⟩, fun N ν β => ?_⟩
  · intro v hv r
    show F' _ ∈ _
    rw [hFF v hv]
    exact hmaps (himg hv) r
  · intro v hv
    obtain ⟨G, hG, hev⟩ := hloc v (himg hv)
    refine ⟨G, hG, ?_⟩
    filter_upwards [hev.filter_mono (nhdsWithin_mono v himg), self_mem_nhdsWithin] with w hw hwD
    refine Eq.trans ?_ hw
    funext _
    exact hFF w hwD
  · obtain ⟨hN, ⟨E₀, -, hE⟩, hmapsC, hcont, hlocC⟩ := hchart N ν β
    obtain ⟨E₁, hE₁, hD'⟩ := hopen
    have hcomp : Continuous fun X : Fin N → ComplexMatrix2 => X ∘ ν :=
      continuous_pi fun b => continuous_apply _
    have hE' : (fun v => v ∘ ν.symm) '' (PeriodicLattice.restrictToPositive B '' D') =
        (fun X : Fin N → ComplexMatrix2 => X ∘ ν) ⁻¹' E₁ ∩
          ComplexMatrix2.complexifiedProduct fun _ : Fin N => ComplexMatrix2.FactorKind.group := by
      ext X
      constructor
      · rintro ⟨v, hv, rfl⟩
        have hv' := hv
        rw [hD'] at hv'
        refine ⟨?_, fun r => hv'.2 (ν.symm r)⟩
        show (v ∘ ν.symm) ∘ ν ∈ E₁
        have : (v ∘ ν.symm) ∘ ν = v := by
          funext b
          simp
        rw [this]
        exact hv'.1
      · rintro ⟨hX₁, hX₂⟩
        refine ⟨X ∘ ν, ?_, ?_⟩
        · rw [hD']
          exact ⟨hX₁, fun b => hX₂ (ν b)⟩
        · funext r
          simp
    have hEE : (fun v => v ∘ ν.symm) '' (PeriodicLattice.restrictToPositive B '' D') ⊆
        (fun v => v ∘ ν.symm) '' (PeriodicLattice.restrictToPositive B '' D) := image_mono himg
    have hX : ∀ X ∈ (fun v => v ∘ ν.symm) '' (PeriodicLattice.restrictToPositive B '' D'),
        F' (PeriodicLattice.extendFromPositive B (X ∘ ν)) =
          F (PeriodicLattice.extendFromPositive B (X ∘ ν)) := by
      rintro X ⟨v, hv, rfl⟩
      have : (v ∘ ν.symm) ∘ ν = v := by
        funext b
        simp
      rw [this]
      exact hFF v hv
    refine ⟨hN, ⟨_, hE₁.preimage hcomp, hE'⟩, ?_, ?_, ?_⟩
    · intro X hXE
      show F' _ ∈ _
      rw [hX X hXE]
      exact hmapsC (hEE hXE)
    · exact (hcont.mono hEE).congr hX
    · intro X hXE
      obtain ⟨W, h0, hW, hhol⟩ := hlocC X (hEE hXE)
      have hchartc := continuous_expChart_tracelessTuple β X
      have hmemW : ∀ w ∈ W ∩ (fun w => ComplexCoordinates.expChart X
            (ComplexCoordinates.tracelessTuple β w)) ⁻¹'
              ((fun X : Fin N → ComplexMatrix2 => X ∘ ν) ⁻¹' E₁),
          ComplexCoordinates.expChart X (ComplexCoordinates.tracelessTuple β w) ∈
            (fun v => v ∘ ν.symm) '' (PeriodicLattice.restrictToPositive B '' D') := by
        rintro w ⟨hwW, hw⟩
        rw [hE']
        have hin := (hW w hwW).1
        rw [hE] at hin
        exact ⟨hw, hin.2⟩
      have hq : ∀ w ∈ W ∩ (fun w => ComplexCoordinates.expChart X
            (ComplexCoordinates.tracelessTuple β w)) ⁻¹'
              ((fun X : Fin N → ComplexMatrix2 => X ∘ ν) ⁻¹' E₁),
          ComplexCoordinates.expChartQuotient
              (fun X => F' (PeriodicLattice.extendFromPositive B (X ∘ ν))) X
              (ComplexCoordinates.tracelessTuple β w) =
            ComplexCoordinates.expChartQuotient
              (fun X => F (PeriodicLattice.extendFromPositive B (X ∘ ν))) X
              (ComplexCoordinates.tracelessTuple β w) := by
        intro w hw
        simp only [ComplexCoordinates.expChartQuotient]
        rw [hX _ (hmemW w hw), hX X hXE]
      refine ⟨W ∩ (fun w => ComplexCoordinates.expChart X
          (ComplexCoordinates.tracelessTuple β w)) ⁻¹'
            ((fun X : Fin N → ComplexMatrix2 => X ∘ ν) ⁻¹' E₁),
        ⟨h0, ?_⟩, fun w hw => ⟨hmemW w hw, ?_⟩, ?_⟩
      · show ComplexCoordinates.expChart X (ComplexCoordinates.tracelessTuple β 0) ∘ ν ∈ E₁
        rw [expChart_tracelessTuple_zero]
        rw [hE'] at hXE
        exact hXE.1
      · rw [hq w hw]
        exact (hW w hw.1).2
      · refine isHolomorphicIn_mono_congr
          (hhol.1.inter ((hE₁.preimage hcomp).preimage hchartc)) inter_subset_left ?_ hhol
        intro w hw
        show ComplexCoordinates.matrixEquiv (ComplexMatrix2.logSeries _) =
          ComplexCoordinates.matrixEquiv (ComplexMatrix2.logSeries _)
        rw [hq w hw]
end Restriction
theorem polydiscInDomainAdmissible_holds (hFields : BondSetFields.ProductStructureHolds)
    (hDouble : PeriodicLattice.DoubleBlockStructure.Statement)
    (hSchemes : PeriodicLattice.AveragingSchemeProperties) :
    PolydiscInDomainAdmissible := by
  intro L hL ρ hρ n k j hn hj c hc hsub hA hC
  obtain ⟨-, hdom, hcen, -, -, hcov⟩ := (hSchemes L hL n k j hn hj .centred).2.1 c hc
  have hsub' : nearIdentityPolydisc ρ c ⊆ PeriodicLattice.schemeHolomorphyDomain .centred c := by
    rw [hcen.domain_eq]
    exact hsub
  have hE := hFields L hL k j hj.le
  have hfin : (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)).Finite :=
    (hE.1 n hn).2.1.subset (subset_univ _)
  have hrev : PeriodicLattice.IsReversalClosed
      (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) :=
    (hDouble L n k j hL hn hj c).1.2.2.1
  have hne : (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)).Nonempty := by
    obtain ⟨b, hb⟩ := (hDouble L n k j hL hn hj c).2.2.1.2
    exact ⟨b, Or.inl hb.1, Or.inr hb.2⟩
  have hP := (hE.1 n hn).1 _ hfin hne hrev
  have hopen : ComplexMatrix2.IsRelativelyOpen
      (ComplexMatrix2.complexifiedProduct fun _ : PeriodicLattice.PositiveBondOf
        (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) =>
          ComplexMatrix2.FactorKind.group)
      (PeriodicLattice.restrictToPositive (PeriodicLattice.bondsInDoubleBlock c) ''
        nearIdentityPolydisc ρ c) := by
    have h := (hP.2.1.2.2.2.2 ρ hρ).2
    have himg : readPositive PeriodicLattice.Bond.IsPositivelyOriented
          (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) ''
        nearIdentity (fieldsOn (PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup)
          (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j))) ρ =
        PeriodicLattice.restrictToPositive (PeriodicLattice.bondsInDoubleBlock c) ''
          nearIdentityPolydisc ρ c := by
      ext v
      constructor
      · rintro ⟨_, ⟨⟨U, hU, rfl⟩, hn'⟩, rfl⟩
        exact ⟨U, ⟨hU, fun b hb => hn' ⟨b, hb⟩⟩, rfl⟩
      · rintro ⟨V, ⟨hV, hn'⟩, rfl⟩
        exact ⟨restrictTo _ V, ⟨⟨V, hV, rfl⟩, fun b => hn' b.1 b.2⟩, rfl⟩
    rw [himg] at h
    exact h
  have hext : ∀ v ∈ PeriodicLattice.restrictToPositive (PeriodicLattice.bondsInDoubleBlock c) ''
      nearIdentityPolydisc ρ c,
      PeriodicLattice.extendFromPositive (PeriodicLattice.bondsInDoubleBlock c) v ∈
        nearIdentityPolydisc ρ c := by
    rintro _ ⟨V, ⟨hV, hnorm⟩, rfl⟩
    have hagree : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)),
        PeriodicLattice.extendFromPositive (PeriodicLattice.bondsInDoubleBlock c)
          (PeriodicLattice.restrictToPositive (PeriodicLattice.bondsInDoubleBlock c) V) b =
            V b := by
      intro b hb
      by_cases hpos : b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) ∧
          b.IsPositivelyOriented
      · simp only [PeriodicLattice.extendFromPositive, dif_pos hpos]
        rfl
      · have hcover := hP.1.2.2 b hb
        have hrp : b.opposite ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) ∧
            b.opposite.IsPositivelyOriented := by
          rcases hcover with ⟨h₁, -⟩ | ⟨⟨e, ⟨he, hre⟩, -⟩, -⟩
          · exact absurd h₁ hpos
          · subst hre
            exact he
        simp only [PeriodicLattice.extendFromPositive, dif_neg hpos, dif_pos hrp]
        show (V b.opposite)⁻¹ = V b
        rw [← hV.2 _ hrp.1]
        rfl
    refine ⟨⟨fun b hb => ?_, fun b hb => ?_⟩, fun b hb => ?_⟩
    · rw [hagree b hb]
      exact hV.1 b hb
    · rw [hagree b hb, hagree _ (hrev b hb)]
      exact hV.2 b hb
    · rw [hagree b hb]
      exact hnorm b hb
  refine ⟨hsub, ?_, ?_, hA, hC, ?_⟩
  · refine isHolomorphicOnFields_mono_congr hsub' hopen (fun v hv => ?_) hdom.average_holomorphic
    exact (hcen.average_eq _ (hsub' (hext v hv))).symm
  · intro y hy x hx
    exact isHolomorphicOnFields_mono_congr hsub' hopen (fun _ _ => rfl)
      (hdom.contour_holomorphic y hy x hx)
  · intro V hV u hu
    have hcv := hcov u V (fun x _ => hu x) hV.1
    have hdV : V ∈ PeriodicLattice.schemeHolomorphyDomain .centred c := hsub' hV
    have hdU : PeriodicLattice.gaugeTransform u V ∈
        PeriodicLattice.schemeHolomorphyDomain .centred c :=
      hcv.average_defined_iff.2 hdV
    refine ⟨?_, ?_, fun y hy x hx => ?_⟩
    · rw [← hcen.domain_eq]
      exact hdU
    · rw [← hcen.average_eq _ hdU, hcv.average_eq hdV, hcen.average_eq _ hdV]
      rfl
    · have hdef : PeriodicLattice.IsContourHolonomyDefined .centred V y x := by
        rcases hy with rfl | hy
        · exact hdV.2.1.1 x hx
        · rw [mem_singleton_iff] at hy
          subst hy
          exact hdV.2.1.2 x hx
      exact hcv.contour_eq y hy x hx hdef
end YangMills.Construction.Tower
end
