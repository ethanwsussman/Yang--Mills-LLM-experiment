import YangMills.Construction.InfiniteLattice.CentredMomentsAtOneIndexAndTheTwoFormsOfVolumeFirstProof
import YangMills.Construction.Cumulants.JointCumulantsOfBoundedRealVariablesProof
import YangMills.Construction.Cumulants.PartitionsMomentsAndTheCentredFunctionalOfAFamily
import YangMills.Construction.InfiniteLattice.CentredIdentityInAState
import YangMills.Construction.TotalDensitiesGiveASystem.FarTranslatesFactoriseOverThePhases
import YangMills.Construction.TotalDensitiesGiveASystem.TheMomentsOfThePhasesAreThoseOfTheComponents
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
open SystemsWithFiveBounds LimitTheorem SeparatedTuples
open InfiniteLattice (GaugeField GaugeFieldProbability IsBoundedObservable
  IsRegularConditionalByIntegrals AmbientSpace centeredMoment ursellPartitionSum
  smearedEnergyCumulant smearedEnergy compactTestFunctions)
open Probability (IsBoundedRealRV)
namespace PhaseMoments
variable {L : ℕ} {IsPair : ℕ+ → ℝ → Prop}
private theorem mem_compactTestFunctions {f : RealValued} (hf : IsC1c f) :
    f ∈ compactTestFunctions := by apply _root_.YangMills.Construction.CutoffLimits.CenteredMomentsAndVolumeFirst.mem_compactTestFunctions_of_isC1c <;> assumption
private theorem isBoundedRealRV_mul {Ω : Type*} [MeasurableSpace Ω] {x y : Ω → ℝ}
    (hx : IsBoundedRealRV x) (hy : IsBoundedRealRV y) :
    IsBoundedRealRV fun ω => x ω * y ω := by apply _root_.YangMills.Construction.Cumulants.RealVariables.isBoundedRealRV_mul <;> assumption
private theorem isBoundedRealRV_centredProduct {a : ℝ}
    (hO : ∀ f ∈ compactTestFunctions,
      IsBoundedRealRV (smearedEnergy f : GaugeField a → ℝ))
    (c : RealValued → ℝ) (l : List RealValued) (hl : ∀ f ∈ l, f ∈ compactTestFunctions) :
    IsBoundedRealRV fun U : GaugeField a =>
      (l.map fun f => smearedEnergy f U - c f).prod := by
  induction l with
  | nil => exact ⟨measurable_const, 1, fun _ => by simp⟩
  | cons f l ih =>
    have h1 := hO f (hl f List.mem_cons_self)
    have h2 := ih fun g hg => hl g (List.mem_cons_of_mem _ hg)
    obtain ⟨C₁, hC₁⟩ := h1.bounded
    have h3 : IsBoundedRealRV fun U : GaugeField a =>
        smearedEnergy f U - c f := by
      refine ⟨h1.measurable.sub_const _, C₁ + |c f|, fun U => ?_⟩
      have h4 := abs_le.1 (hC₁ U)
      have h5 := le_abs_self (c f)
      have h6 := neg_abs_le (c f)
      exact abs_le.2 ⟨by linarith [h4.1], by linarith [h4.2]⟩
    simpa only [List.map_cons, List.prod_cons] using isBoundedRealRV_mul h3 h2
private theorem isBoundedRealRV_smearedEnergy (hCent : InfiniteLattice.CenteredIdentity.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (Q : PairSequence L IsPair) (j : ℕ+)
    (f : RealValued) (hf : f ∈ compactTestFunctions) :
    IsBoundedRealRV (smearedEnergy f : FieldAt Q j → ℝ) :=
  ((hCent ⟨L, hL, Q.cutoff j, 1⟩ (Q.state j) (Q.isLimit j).1).1.1 f hf).2
private theorem isBoundedRealRV_centeredRep (hCent : InfiniteLattice.CenteredIdentity.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (Q : PairSequence L IsPair) (j : ℕ+) (T : SepTuple) :
    IsBoundedRealRV (CenteredRepresentatives.centeredRep L (Q.cutoff j) (Q.state j) T) :=
  isBoundedRealRV_centredProduct (isBoundedRealRV_smearedEnergy hCent hL Q j) _ T.1
    fun _ hf => mem_compactTestFunctions (T.2.1 _ hf)
private theorem isBoundedObservable_centeredRep
    (hCent : InfiniteLattice.CenteredIdentity.Statement) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (Q : PairSequence L IsPair) (j : ℕ+) (T : SepTuple) :
    IsBoundedObservable (a := PeriodicLattice.meshSize L (((Q.cutoff j : ℕ)) : ℤ))
      fun U => ((CenteredRepresentatives.centeredRep L (Q.cutoff j) (Q.state j) T U : ℝ) : ℂ) := by
  have hB := isBoundedRealRV_centeredRep hCent hL Q j T
  obtain ⟨C, hC⟩ := hB.bounded
  refine ⟨Complex.measurable_ofReal.comp hB.measurable, C, fun U => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hC U
private theorem expect_eq_centredMean (Q : PairSequence L IsPair) (j : ℕ+)
    (ρ : GaugeFieldProbability (PeriodicLattice.meshSize L (((Q.cutoff j : ℕ)) : ℤ))) (T : SepTuple) :
    ρ.expect (fun U => ((CenteredRepresentatives.centeredRep L (Q.cutoff j) (Q.state j) T U : ℝ) : ℂ)) =
      ((centredMean Q j ρ.1 T : ℝ) : ℂ) :=
  integral_complex_ofReal
private theorem isBoundedRealRV_centredMean (hCent : InfiniteLattice.CenteredIdentity.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (Q : PairSequence L IsPair)
    {κ : ∀ j, FieldAt Q j → GaugeFieldProbability (PeriodicLattice.meshSize L (((Q.cutoff j : ℕ)) : ℤ))}
    (hκ : IsConditionalKernel Q κ) (j : ℕ+) (T : SepTuple) :
    IsBoundedRealRV fun U => centredMean Q j (κ j U).1 T := by
  have hF := isBoundedObservable_centeredRep hCent hL Q j T
  have hm : Measurable fun U => (κ j U).expect
      (fun U => ((CenteredRepresentatives.centeredRep L (Q.cutoff j) (Q.state j) T U : ℝ) : ℂ)) :=
    Measurable.mono ((hκ j _ hF).1) (fun s hs => hs.1) le_rfl
  obtain ⟨C, hC⟩ := (isBoundedRealRV_centeredRep hCent hL Q j T).bounded
  refine ⟨?_, C, fun U => ?_⟩
  · have he : (fun U => centredMean Q j (κ j U).1 T) = fun U => ((κ j U).expect
        (fun U => ((CenteredRepresentatives.centeredRep L (Q.cutoff j) (Q.state j) T U : ℝ) : ℂ))).re := by
      funext U
      rw [expect_eq_centredMean, Complex.ofReal_re]
    rw [he]
    exact Complex.measurable_re.comp hm
  · have := (κ j U).2
    have h := norm_integral_le_of_norm_le_const (μ := (κ j U).1) (C := C)
      (f := CenteredRepresentatives.centeredRep L (Q.cutoff j) (Q.state j) T)
      (Eventually.of_forall fun V => by simpa [Real.norm_eq_abs] using hC V)
    simpa [centredMean, Real.norm_eq_abs] using h
private theorem isBoundedRealRV_prod_centredMean (hCent : InfiniteLattice.CenteredIdentity.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (Q : PairSequence L IsPair)
    {κ : ∀ j, FieldAt Q j → GaugeFieldProbability (PeriodicLattice.meshSize L (((Q.cutoff j : ℕ)) : ℤ))}
    (hκ : IsConditionalKernel Q κ) (j : ℕ+) (W : List SepTuple) :
    IsBoundedRealRV fun U => (W.map fun Z => centredMean Q j (κ j U).1 Z).prod := by
  induction W with
  | nil => exact ⟨measurable_const, 1, fun _ => (abs_one (α := ℝ)).le⟩
  | cons Z W ih => exact isBoundedRealRV_mul (isBoundedRealRV_centredMean hCent hL Q hκ j Z) ih
private theorem integrable_of_isBoundedRealRV (Q : PairSequence L IsPair) (j : ℕ+)
    {x : FieldAt Q j → ℝ} (hx : IsBoundedRealRV x) :
    Integrable x (Q.state j) := by
  have : IsProbabilityMeasure (Q.state j) := (Q.isLimit j).1
  obtain ⟨C, hC⟩ := hx.bounded
  exact Integrable.of_bound hx.measurable.aestronglyMeasurable C
    (Eventually.of_forall fun U => by simpa [Real.norm_eq_abs] using hC U)
private theorem integral_centredMean (hCent : InfiniteLattice.CenteredIdentity.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (Q : PairSequence L IsPair)
    {κ : ∀ j, FieldAt Q j → GaugeFieldProbability (PeriodicLattice.meshSize L (((Q.cutoff j : ℕ)) : ℤ))}
    (hκ : IsConditionalKernel Q κ) (j : ℕ+) (T : SepTuple) :
    ∫ U, centredMean Q j (κ j U).1 T ∂Q.state j =
      ∫ U, CenteredRepresentatives.centeredRep L (Q.cutoff j) (Q.state j) T U ∂Q.state j := by
  have h := (hκ j _ (isBoundedObservable_centeredRep hCent hL Q j T)).2 (fun _ => 1)
    measurable_const ⟨1, fun _ => by simp⟩
  simp only [one_mul, expect_eq_centredMean] at h
  rw [integral_complex_ofReal, integral_complex_ofReal] at h
  exact Complex.ofReal_injective h
private theorem ofReal_integral_centeredRep
    (hCent : InfiniteLattice.CenteredIdentity.Statement) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (Q : PairSequence L IsPair) (j : ℕ+) (T : SepTuple) :
    ((∫ U, CenteredRepresentatives.centeredRep L (Q.cutoff j) (Q.state j) T U ∂Q.state j : ℝ) : ℂ) =
      ∑ π ∈ (SetPartition.atLeastTwoPartitions
          (Finset.univ : Finset (Fin (TupleLists.ofList T).1))).attach,
        ∏ J ∈ π.1.parts.attach,
          smearedEnergyCumulant (Q.state j) (TestSpaces.sepRestrict (TupleLists.ofList T).2 J.1).1 := by
  have hprob : IsProbabilityMeasure (Q.state j) := (Q.isLimit j).1
  have hid := (hCent ⟨L, hL, Q.cutoff j, 1⟩ (Q.state j) hprob).2.2 T.1.length T.1.get
    fun l => mem_compactTestFunctions (T.2.1 _ (List.get_mem T.1 l))
  have hmoment : ((∫ U, CenteredRepresentatives.centeredRep L (Q.cutoff j) (Q.state j) T U ∂Q.state j : ℝ) : ℂ) =
      centeredMoment (Q.state j) T.1.get := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun U => ?_)
    change (((T.1.map fun f => smearedEnergy f U - ∫ V, smearedEnergy f V ∂Q.state j).prod : ℝ) : ℂ) =
      ∏ l : Fin T.1.length, (((smearedEnergy (T.1.get l) U : ℝ) : ℂ) -
        ∫ V, ((smearedEnergy (T.1.get l) V : ℝ) : ℂ) ∂Q.state j)
    rw [← Fin.prod_univ_fun_getElem, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [integral_complex_ofReal, Complex.ofReal_sub]
    rfl
  rw [hmoment]
  refine hid.trans ?_
  unfold ursellPartitionSum
  rw [SetPartition.nonSingletonPartitions_eq_atLeastTwoPartitions, ← Finset.sum_attach]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← Finset.prod_attach]
  rfl
private theorem tendsto_integral_centeredRep
    (hCent : InfiniteLattice.CenteredIdentity.Statement) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (Q : PairSequence L IsPair) {S : CumulantFamily} (hS : Q.Defines S) (T : SepTuple) :
    Tendsto (fun j => ∫ U, CenteredRepresentatives.centeredRep L (Q.cutoff j) (Q.state j) T U ∂Q.state j) atTop
      (𝓝 (centredOf S T)) := by
  have hval : centredOf S T =
      TestSpaces.blockProductSum S (TupleLists.ofList T) :=
    TestSpaces.centredOfCumulants_eq_blockProductSum S (TupleLists.ofList T)
  have hc : Tendsto (fun j =>
      ((∫ U, CenteredRepresentatives.centeredRep L (Q.cutoff j) (Q.state j) T U ∂Q.state j : ℝ) : ℂ)) atTop
      (𝓝 ((centredOf S T : ℝ) : ℂ)) := by
    simp only [ofReal_integral_centeredRep hCent hL Q]
    rw [hval, TestSpaces.blockProductSum]
    push_cast
    refine tendsto_finsetSum _ fun π _ => tendsto_finsetProd _ fun J _ => ?_
    exact hS _ _ _
  exact (Complex.continuous_re.tendsto _).comp hc
private theorem centredMean_congr_perm (Q : PairSequence L IsPair) (j : ℕ+)
    (ρ : Measure (FieldAt Q j)) {A B : SepTuple} (h : A.1.Perm B.1) :
    centredMean Q j ρ A = centredMean Q j ρ B := by
  have he : ∀ U, CenteredRepresentatives.centeredRep L (Q.cutoff j) (Q.state j) A U =
      CenteredRepresentatives.centeredRep L (Q.cutoff j) (Q.state j) B U := fun U =>
    (h.map _).prod_eq
  simp only [centredMean, he]
private theorem centredMean_shiftedJuxt (Q : PairSequence L IsPair) (j : ℕ+)
    (ρ : Measure (FieldAt Q j)) {X : SepTuple} {Y : List SepTuple} {k : ℕ} (hk : k < Y.length)
    {vs : List AmbientSpace} {v : AmbientSpace} (hvs : vs ∈ iterLimitDomain X Y Set.univ (k + 1))
    (hv : v :: vs ∈ iterLimitDomain X Y Set.univ k) :
    centredMean Q j ρ (shiftedJuxt X ((Y.drop k).zip (v :: vs))) =
      centredMean Q j ρ (SepTuple.juxt (shiftedJuxt X ((Y.drop (k + 1)).zip vs))
        (push (translate v) Y[k])) := by
  have hzip : (Y.drop k).zip (v :: vs) = (Y[k], v) :: (Y.drop (k + 1)).zip vs := by
    rw [List.drop_eq_getElem_cons hk, List.zip_cons_cons]
  have hsep := hv.2.2
  have hval := shiftedJuxt_val hsep
  have hT := shiftedJuxt_val hvs.2.2
  have hperm : (shiftedComponents X ((Y.drop k).zip (v :: vs))).Perm
      ((shiftedJuxt X ((Y.drop (k + 1)).zip vs)).1 ++ (push (translate v) Y[k]).1) := by
    rw [hT, hzip]
    simp only [shiftedComponents, List.flatMap_cons, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm
  have hdef : SepTuple.Composable (shiftedJuxt X ((Y.drop (k + 1)).zip vs))
      (push (translate v) Y[k]) :=
    (List.pairwise_append.1 (hsep.perm hperm).2).2.2
  refine centredMean_congr_perm Q j ρ ?_
  rw [hval, SepTuple.juxt_val hdef]
  exact hperm
private theorem prod_map_concat {α : Type*} (f : α → ℝ) (l : List α) (a : α) :
    ((l ++ [a]).map f).prod = (l.map f).prod * f a := by
  simp
private def stageMoment (Q : PairSequence L IsPair)
    (κ : ∀ j, FieldAt Q j → GaugeFieldProbability (PeriodicLattice.meshSize L (((Q.cutoff j : ℕ)) : ℤ)))
    (X : SepTuple) (Y : List SepTuple) (k : ℕ) (vs : List AmbientSpace) (j : ℕ+) : ℝ :=
  ∫ U, centredMean Q j (κ j U).1 (shiftedJuxt X ((Y.drop k).zip vs)) *
    ((Y.take k).map fun Z => centredMean Q j (κ j U).1 Z).prod ∂Q.state j
private def diagonalPoint (n : ℕ) : AmbientSpace :=
  latticePoint fun _ => (n : ℤ)
private theorem tendsto_diagonalPoint : Tendsto diagonalPoint atTop (atInfinityWithin Set.univ) := by
  rw [atInfinityWithin_univ]
  show Tendsto diagonalPoint atTop (comap TorusMetric.euclidNormVec atTop)
  rw [tendsto_comap_iff]
  refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
  refine Real.le_sqrt_of_sq_le ?_
  have h : 0 ≤ (n : ℝ) ^ 2 := by positivity
  simp [diagonalPoint, latticePoint]
  linarith
private theorem tendsto_stageMoment (hFar : farTranslatesFactorStatement)
    (hCent : InfiniteLattice.CenteredIdentity.Statement) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (Q : PairSequence L IsPair) {S : CumulantFamily} (hβ : ∀ j, 0 < Q.coupling j)
    (hS : Q.Defines S)
    {κ : ∀ j, FieldAt Q j → GaugeFieldProbability (PeriodicLattice.meshSize L (((Q.cutoff j : ℕ)) : ℤ))}
    (hκ : IsConditionalKernel Q κ) (X : SepTuple) (Y : List SepTuple)
    (hlim : IterLimitsExist (centredOf S) X Y Set.univ) (k : ℕ) :
    k ≤ Y.length → ∀ vs ∈ iterLimitDomain X Y Set.univ k,
      Tendsto (stageMoment Q κ X Y k vs) atTop
        (𝓝 (iterLimitValue (centredOf S) X Y Set.univ k vs)) := by
  induction k with
  | zero =>
    intro _ vs _
    have he : stageMoment Q κ X Y 0 vs = fun j => ∫ U, CenteredRepresentatives.centeredRep L
        (Q.cutoff j) (Q.state j) (shiftedJuxt X (Y.zip vs)) U ∂Q.state j := by
      funext j
      rw [← integral_centredMean hCent hL Q hκ]
      exact integral_congr_ae (Eventually.of_forall fun U => mul_one _)
    rw [he]
    exact tendsto_integral_centeredRep hCent hL Q hS _
  | succ k ih =>
    intro hk vs hvs
    have hk' : k < Y.length := hk
    have hc := tendsto_iterLimitValue hlim hk' hvs
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε3 : 0 < ε / 3 := by positivity
    obtain ⟨R, hR⟩ := hFar L hL IsPair Q S hβ hS κ hκ
      (shiftedJuxt X ((Y.drop (k + 1)).zip vs)) Y[k] (Y.take k) (ε / 3) hε3
    have hev := (hc.eventually (Metric.ball_mem_nhds _ hε3)).and
      (eventually_cons_mem_iterLimitDomain X Y Set.univ hk' hvs)
    obtain ⟨n, ⟨hn₁, hn₂⟩, hn₃⟩ :=
      ((tendsto_diagonalPoint.eventually hev).and (eventually_ge_atTop R)).exists
    have hj := ih hk'.le (diagonalPoint n :: vs) hn₂
    filter_upwards [Metric.tendsto_nhds.1 hj (ε / 3) hε3] with j hj'
    have hbound := hR (fun _ => (n : ℤ)) ⟨0, by simpa using hn₃⟩ j
    have hdiff : stageMoment Q κ X Y k (diagonalPoint n :: vs) j -
        stageMoment Q κ X Y (k + 1) vs j =
        ∫ U, (centredMean Q j (κ j U).1 (SepTuple.juxt (shiftedJuxt X ((Y.drop (k + 1)).zip vs))
              (push (translate (diagonalPoint n)) Y[k])) -
            centredMean Q j (κ j U).1 (shiftedJuxt X ((Y.drop (k + 1)).zip vs)) *
              centredMean Q j (κ j U).1 Y[k]) *
          ((Y.take k).map fun Z => centredMean Q j (κ j U).1 Z).prod ∂Q.state j := by
      have hi₁ := integrable_of_isBoundedRealRV Q j (isBoundedRealRV_mul
        (isBoundedRealRV_centredMean hCent hL Q hκ j (shiftedJuxt X ((Y.drop k).zip (diagonalPoint n :: vs))))
        (isBoundedRealRV_prod_centredMean hCent hL Q hκ j (Y.take k)))
      have hi₂ := integrable_of_isBoundedRealRV Q j (isBoundedRealRV_mul
        (isBoundedRealRV_centredMean hCent hL Q hκ j (shiftedJuxt X ((Y.drop (k + 1)).zip vs)))
        (isBoundedRealRV_prod_centredMean hCent hL Q hκ j (Y.take (k + 1))))
      rw [stageMoment, stageMoment, ← integral_sub hi₁ hi₂]
      refine integral_congr_ae (Eventually.of_forall fun U => ?_)
      have htake : Y.take (k + 1) = Y.take k ++ [Y[k]] := (List.take_concat_get' Y k hk').symm
      have hp : ((Y.take (k + 1)).map fun Z => centredMean Q j (κ j U).1 Z).prod =
          ((Y.take k).map fun Z => centredMean Q j (κ j U).1 Z).prod * centredMean Q j (κ j U).1 Y[k] := by
        rw [htake]
        exact prod_map_concat _ _ _
      show centredMean Q j (κ j U).1 (shiftedJuxt X ((Y.drop k).zip (diagonalPoint n :: vs))) *
            ((Y.take k).map fun Z => centredMean Q j (κ j U).1 Z).prod -
          centredMean Q j (κ j U).1 (shiftedJuxt X ((Y.drop (k + 1)).zip vs)) *
            ((Y.take (k + 1)).map fun Z => centredMean Q j (κ j U).1 Z).prod = _
      rw [centredMean_shiftedJuxt Q j (κ j U).1 hk' hvs hn₂, hp]
      ring
    have h₁ : dist (stageMoment Q κ X Y (k + 1) vs j)
        (stageMoment Q κ X Y k (diagonalPoint n :: vs) j) ≤ ε / 3 := by
      rw [dist_comm, Real.dist_eq, hdiff]
      exact hbound
    have h₂ : dist (iterLimitValue (centredOf S) X Y Set.univ k (diagonalPoint n :: vs))
        (iterLimitValue (centredOf S) X Y Set.univ (k + 1) vs) < ε / 3 := hn₁
    calc dist (stageMoment Q κ X Y (k + 1) vs j)
          (iterLimitValue (centredOf S) X Y Set.univ (k + 1) vs)
        ≤ dist (stageMoment Q κ X Y (k + 1) vs j)
            (stageMoment Q κ X Y k (diagonalPoint n :: vs) j) +
          dist (stageMoment Q κ X Y k (diagonalPoint n :: vs) j)
            (iterLimitValue (centredOf S) X Y Set.univ k (diagonalPoint n :: vs)) +
          dist (iterLimitValue (centredOf S) X Y Set.univ k (diagonalPoint n :: vs))
            (iterLimitValue (centredOf S) X Y Set.univ (k + 1) vs) :=
          dist_triangle4 _ _ _ _
      _ < ε := by linarith
theorem phaseMomentsConverge (hFar : farTranslatesFactorStatement)
    (hCent : InfiniteLattice.CenteredIdentity.Statement) : phaseMomentsConvergeStatement := by
  intro L hL IsPair Q S hβ hS κ hκ A hA X Y
  have h := tendsto_stageMoment hFar hCent hL Q hβ hS hκ X Y (hA.iterLimits_exist X Y) Y.length le_rfl []
    (by rw [iterLimitDomain_length]; rfl)
  have he : phaseMoment Q κ X Y = stageMoment Q κ X Y Y.length [] := by
    funext j
    simp [stageMoment, phaseMoment, shiftedJuxt]
  rw [hA.integral_comp_prod X Y, he]
  exact h
end PhaseMoments
end YangMills.Construction.TotalDensitiesGiveASystem
end
