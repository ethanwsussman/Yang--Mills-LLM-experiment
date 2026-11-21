import YangMills.Construction.ClusterExpansionOfAStep.FourCornersProof
import YangMills.Construction.ClusterExpansionOfAStep.PotentialOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.SizeOfJOfASettingProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.StepSettings
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepCosts
namespace PotentialFactorization
section Corners
variable {F : BlockFrame}
theorem card_plaquetteCorners (hL : 0 < F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) {j : ℕ}
    (x : F.Site j) {μ ν : Fin 4} (h : μ ≠ ν) : (plaquetteCorners (x, μ, ν)).card = 4 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellShares.card_plaquetteCorners <;> assumption
theorem innerPlaquettes_directions_ne {S : Finset F.Cell} {p : F.Site 0 × Fin 4 × Fin 4}
    (hp : p ∈ innerPlaquettes S 0) : p.2.1 ≠ p.2.2 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CellShares.ne_of_mem_innerPlaquettes <;> assumption
theorem sum_ite_eq_const {β : Type} [Fintype β] (y : β) (c : ℝ) [∀ Y, Decidable (y = Y)] :
    ∑ Y : β, (if y = Y then c else 0) = c := by
  rw [Finset.sum_eq_single y]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
  · intro h
    exact absurd (Finset.mem_univ y) h
theorem sum_cellShare [Fintype F.Cell] (hL : 0 < F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (a : ℝ)
    (S : Finset F.Cell) (X : F.FieldChain) :
    ∑ Y : F.Cell, cellShare a S Y X = chainAction a S X := by
  classical
  unfold cellShare chainAction BlockAverages.wilsonAction
  rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    rw [← Finset.sum_mul]
    have hq : ∑ Y : F.Cell, ∑ x ∈ plaquetteCorners p,
        (if enclosingCell x = Y then (1 / 4 : ℝ) else 0) = 1 := by
      rw [Finset.sum_comm]
      simp only [sum_ite_eq_const, Finset.sum_const, nsmul_eq_mul]
      obtain ⟨x, μ, ν⟩ := p
      rw [card_plaquetteCorners hL hs x (innerPlaquettes_directions_ne hp)]
      norm_num
    rw [hq, one_mul]
  · congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    rw [← Finset.sum_mul, Finset.sum_add_distrib, sum_ite_eq_const, sum_ite_eq_const]
    norm_num
theorem sum_minimalCellShare [Fintype F.Cell] (hLV : minimalChainExistenceStatement)
    (hL : 0 < F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (a : ℝ) (ha : 0 ≤ a) (S : Finset F.Cell)
    (V : F.GaugeField F.top) :
    ∑ Y : F.Cell, minimalCellShare a S Y V = minimalAction a S F.top V := by
  classical
  obtain ⟨X₀, hX₀, htot⟩ := (hLV F a S ha).2.2.2 V
  have hex : ∃ X, IsMinimalChain a S V X := ⟨X₀, hX₀⟩
  have hshare : ∀ Y, minimalCellShare a S Y V = cellShare a S Y hex.choose := by
    intro Y
    unfold minimalCellShare
    rw [dif_pos hex]
  simp only [hshare]
  rw [sum_cellShare hL hs, ← htot]
  exact le_antisymm (hex.choose_spec.2 X₀ hX₀.1) (hX₀.2 _ hex.choose_spec.1)
end Corners
section Torus
variable {n : ℕ}
theorem zmod_cast_cast {m k : ℕ} (hm : m = k) [NeZero m] (a : ZMod m) :
    ((((a.cast : ℤ) : ZMod k).cast : ℤ) : ZMod m) = a := by apply _root_.YangMills.Construction.WeightedResponses.intCast_cast_intCast_cast_of_eq <;> assumption
theorem torusSiteInFrame_bijective [NeZero n] (F : BlockFrame) (j : ℕ) (hper : ∀ i, F.period j i = n) :
    Function.Bijective (torusSiteInFrame (n := n) F j) := by
  have hne : ∀ i, NeZero (F.period j i) := fun i => ⟨by
    rw [hper]
    exact NeZero.ne n⟩
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun z i => (((z i).cast : ℤ) : ZMod n), fun x => ?_, fun z => ?_⟩
  · funext i
    exact zmod_cast_cast (hper i).symm (x i)
  · funext i
    have := hne i
    exact zmod_cast_cast (hper i) (z i)
theorem sum_count_eq_length {α : Type} [Fintype α] [DecidableEq α] (l : List α) :
    ∑ y : α, l.count y = l.length := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.FourCornerProof.sum_count_eq_length <;> assumption
variable [NeZero n]
theorem sum_levelShare (hLV : minimalChainExistenceStatement) (a : ℝ) (ha : 0 ≤ a)
    (L : ℕ) (hL : 0 < L) (hn : 2 ≤ n) (t : ℕ) (S : Finset (TorusSite n)) (W : TorusField n) :
    ∑ y : TorusSite n, levelShare a L t S y W = actionAtLevel a L t S W := by
  classical
  cases t with
  | zero =>
    simp only [levelShare, actionAtLevel, TorusFields.wilsonAction]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [← Finset.sum_mul, ← Finset.sum_div, ← Nat.cast_sum, sum_count_eq_length]
    simp [plaquetteVertices]
  | succ t =>
    have hper : ∀ i, (torusFrame L t n).period (t + 1) i = n := fun i => by
      simp [BlockFrame.period, torusFrame, BlockFrame.top]
    have hb := torusSiteInFrame_bijective (n := n) (torusFrame L t n) (t + 1) hper
    let i₁ : Fintype (torusFrame L t n).Cell := Fintype.ofBijective _ hb
    simp only [levelShare, actionAtLevel]
    have hs : ∀ i, 2 ≤ (torusFrame L t n).extent i := fun _ => hn
    have h1 := sum_minimalCellShare (F := torusFrame L t n) hLV hL hs a ha
      (cellsOfSites (torusFrame L t n) S) (readAtLevel (torusFrame L t n) (t + 1) W)
    refine Eq.trans ?_ h1
    exact @Fintype.sum_bijective (TorusSite n) (torusFrame L t n).Cell ℝ _ i₁ _ _ hb _ _ fun _ => rfl
theorem sum_sitesInBlocks (L : ℕ) [NeZero L] (g : TorusSite (n * L) → ℝ) :
    ∑ Y : TorusSite n, ∑ y ∈ sitesInBlocks L {Y}, g y = ∑ y, g y := by apply _root_.YangMills.Construction.FreeBonds.sum_sitesInBlocks_singleton <;> assumption
end Torus
section Sizes
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖(toImaginary v : ℍ[ℝ])‖ = ‖v‖ := by apply _root_.YangMills.Construction.BlockTrees.norm_toImaginary <;> assumption
theorem norm_toCoords (w : imaginaryQuaternions) : ‖toCoords w‖ = ‖(w : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogJacobianBound.norm_toCoords <;> assumption
theorem haarLogDensity_pos {v : EuclideanSpace ℝ (Fin 3)} (h : ‖v‖ < Real.pi) :
    0 < haarLogDensity v := by
  unfold haarLogDensity
  rw [if_pos h]
  have hs : Real.sinc ‖v‖ ≠ 0 := by
    by_cases h0 : ‖v‖ = 0
    · rw [h0, Real.sinc_zero]
      exact one_ne_zero
    · have hp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm h0)
      rw [Real.sinc_of_ne_zero h0]
      exact div_ne_zero (Real.sin_pos_of_pos_of_lt_pi hp h).ne' h0
  have := Real.pi_pos
  positivity
theorem norm_frame_le {R : StepSetup} {n : ℕ} (hρ : 0 ≤ R.anchorRadius) (s : ChartSetting R n)
    (b : TorusBond (n * R.params.side)) : ‖(s.frame b : ℍ[ℝ])‖ ≤ R.anchorRadius := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogJacobianBound.norm_frame_le <;> assumption
end Sizes
end PotentialFactorization
open PotentialFactorization in
theorem potentialFactorization_holds (hLV : minimalChainExistenceStatement)
    (hK : BondKernelProperties) : PotentialFactorization := by
  classical
  intro R hfit hrow hρA hπ n _ hn s hs η hη
  obtain ⟨hcold, hhull⟩ := hrow
  have hLpos : 0 < R.params.side := NeZero.pos _
  have hnL : R.params.n₀ ≤ n * R.params.side := hn.trans (Nat.le_mul_of_pos_right _ hLpos)
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  have hD1 : 0 < R.functional (n * R.params.side) (trivialField (n * R.params.side)) := by
    apply hcold.positive _ hnL
    intro x μ ν _
    simp [curvature, holonomy, trivialField, hfit.σ_pos]
  have hform := hhull.form (n * R.params.side) hside (s.field η) s.support s.labelling (hs.isHull η hη)
  have hJ : ∀ b : s.free, 0 < haarLogDensity (toCoords (s.frame b.1) + η b) := by
    intro b
    apply haarLogDensity_pos
    have h1 := norm_add_le (toCoords (s.frame b.1)) (η b)
    rw [norm_toCoords] at h1
    have h2 := norm_frame_le hρA.le s b.1
    have h3 := hη b
    unfold coordNorm at h3
    rw [norm_toImaginary] at h3
    linarith
  have hJpos : 0 < s.haarJacobian η := Finset.prod_pos fun b _ => hJ b
  have hJexp : s.haarJacobian η =
      Real.exp (∑ b : s.free, Real.log (haarLogDensity (toCoords (s.frame b.1) + η b))) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun b _ => (Real.exp_log (hJ b)).symm
  have hk := fun c => hK.2 R.params R.coupling n
    (readAtLevel (stepBlockFrame R.params.side n) 0 (s.field η))
    (readAtLevel (stepBlockFrame R.params.side n) 1 s.coarse) s.bases c
  have hKpos : 0 < s.kernelProduct η := Finset.prod_pos fun c _ => (hk c).1
  have hKexp : s.kernelProduct η = Real.exp (∑ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
      Real.log (bondKernel R.params R.coupling
        (readAtLevel (stepBlockFrame R.params.side n) 0 (s.field η))
        (readAtLevel (stepBlockFrame R.params.side n) 1 s.coarse) s.bases c)) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun c _ => (Real.exp_log (hk c).1).symm
  have hper : ∀ i, (stepBlockFrame R.params.side n).period 1 i = n := fun i => by
    simp [BlockFrame.period, stepBlockFrame, BlockFrame.top]
  have hb := torusSiteInFrame_bijective (n := n) (stepBlockFrame R.params.side n) 1 hper
  have hbp : Function.Bijective
      (Prod.map (torusSiteInFrame (n := n) (stepBlockFrame R.params.side n) 1) (id : Fin 4 → Fin 4)) :=
    hb.prodMap Function.bijective_id
  have hlog : ∑ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
      Real.log (bondKernel R.params R.coupling
        (readAtLevel (stepBlockFrame R.params.side n) 0 (s.field η))
        (readAtLevel (stepBlockFrame R.params.side n) 1 s.coarse) s.bases c) =
      ∑ Y : TorusSite n, ∑ i : Fin 4,
        (-(R.params.coupling * R.coupling) * bondFit R.params (s.field η) s.coarse s.bases (Y, i) +
        logPartitionGap (R.params.coupling * R.coupling *
          meanNorm R.params (s.field η) s.bases (Y, i))) := by
    rw [← Fintype.sum_prod_type']
    symm
    refine Fintype.sum_bijective _ hbp _ _ fun c => ?_
    exact (hk _).2.1.symm
  have hfits : ∑ Y : TorusSite n, ∑ i : Fin 4, (bondFit R.params (s.field η) s.coarse s.bases (Y, i) +
        bondFit R.params (s.field η) s.coarse s.bases (Y - TorusFields.unitStep n i, i)) =
      2 * ∑ Y : TorusSite n, ∑ i : Fin 4, bondFit R.params (s.field η) s.coarse s.bases (Y, i) := by
    simp only [Finset.sum_add_distrib]
    have : ∑ Y : TorusSite n, ∑ i : Fin 4,
        bondFit R.params (s.field η) s.coarse s.bases (Y - TorusFields.unitStep n i, i) =
        ∑ Y : TorusSite n, ∑ i : Fin 4, bondFit R.params (s.field η) s.coarse s.bases (Y, i) := by
      rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact Fintype.sum_equiv (Equiv.subRight (TorusFields.unitStep n i)) _ _ fun _ => rfl
    rw [this]
    ring
  have hcost : ∑ Y : TorusSite n, blockCost R.params R.depth (s.field η) s.coarse s.bases Y =
      actionAtLevel R.params.coupling R.params.side R.depth
        (Finset.univ \ thickening lumpRange (torusHotSites R.params (s.field η))) (s.field η) +
        R.params.coupling *
          ∑ Y : TorusSite n, ∑ i : Fin 4, bondFit R.params (s.field η) s.coarse s.bases (Y, i) := by
    unfold blockCost
    rw [Finset.sum_add_distrib, sum_sitesInBlocks, ← Finset.mul_sum, hfits,
      sum_levelShare hLV _ (by linarith [hfit.a_ge]) _ hLpos
        (by have := hfit.n₀_ge; omega)]
    ring
  have hphi : ∑ Y : TorusSite n, s.blockDensity (s.field η) Y =
      ∑ y, R.siteDensity (n * R.params.side) y (s.field η) s.support s.labelling := by
    unfold ChartSetting.blockDensity
    exact sum_sitesInBlocks _ _
  have hj : ∑ Y : TorusSite n, s.logJacobian (s.field η) η Y =
      ∑ Y : TorusSite n, ∑ i : Fin 4, logPartitionGap (R.params.coupling * R.coupling *
          meanNorm R.params (s.field η) s.bases (Y, i)) +
        ∑ b : s.free, Real.log (haarLogDensity (toCoords (s.frame b.1) + η b)) := by
    unfold ChartSetting.logJacobian
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    simp
  have hpot : s.potential η =
      R.coupling * actionAtLevel R.params.coupling R.params.side R.depth
        (Finset.univ \ thickening lumpRange (torusHotSites R.params (s.field η))) (s.field η) -
        (∑ y, R.siteDensity (n * R.params.side) y (s.field η) s.support s.labelling) -
        (∑ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
          Real.log (bondKernel R.params R.coupling
            (readAtLevel (stepBlockFrame R.params.side n) 0 (s.field η))
            (readAtLevel (stepBlockFrame R.params.side n) 1 s.coarse) s.bases c)) -
        ∑ b : s.free, Real.log (haarLogDensity (toCoords (s.frame b.1) + η b)) := by
    unfold ChartSetting.potential
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hcost, hphi, hj, hlog]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  set E₁ := -R.coupling * actionAtLevel R.params.coupling R.params.side R.depth
        (Finset.univ \ thickening lumpRange (torusHotSites R.params (s.field η))) (s.field η) +
        ∑ y, R.siteDensity (n * R.params.side) y (s.field η) s.support s.labelling with hE₁
  set E₂ := ∑ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
          Real.log (bondKernel R.params R.coupling
            (readAtLevel (stepBlockFrame R.params.side n) 0 (s.field η))
            (readAtLevel (stepBlockFrame R.params.side n) 1 s.coarse) s.bases c) with hE₂
  set E₃ := ∑ b : s.free, Real.log (haarLogDensity (toCoords (s.frame b.1) + η b)) with hE₃
  have hsum : -s.potential η = E₁ + E₂ + E₃ := by
    rw [hpot, hE₁]
    ring
  have hform' : R.labelWeight (n * R.params.side) (s.field η) s.support s.labelling =
      R.functional (n * R.params.side) (trivialField (n * R.params.side)) * Real.exp E₁ *
        ∏ X ∈ chainComponents R.range s.support,
          R.clusterFactor (n * R.params.side) (s.field η) s.support s.labelling X := hform
  have he : Real.exp (E₁ + E₂ + E₃) = Real.exp E₁ * Real.exp E₂ * Real.exp E₃ := by
    rw [Real.exp_add, Real.exp_add]
  refine ⟨hD1, hKpos, hJpos, ?_, ?_⟩
  · rw [hform', hKexp, hJexp, hsum, he]
    ring
  · intro hΦ
    have hq : R.labelWeight (n * R.params.side) (s.field η) s.support s.labelling /
        (R.functional (n * R.params.side) (trivialField (n * R.params.side)) *
        ∏ X ∈ chainComponents R.range s.support,
          R.clusterFactor (n * R.params.side) (s.field η) s.support s.labelling X) = Real.exp E₁ := by
      rw [hform']
      field_simp
    rw [hq, hKexp, hJexp, ← Real.exp_add, ← Real.exp_add, Real.log_exp]
    linarith
end YangMills.Construction.StepSettings
end
