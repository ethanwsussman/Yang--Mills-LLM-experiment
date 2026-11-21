import YangMills.Construction.ForwardTube.ArgumentsOfTheGramKernelInTheShiftedTubes
import YangMills.Construction.RotationInvariance.GramKernelStaysPositiveAtImaginaryAngles
import YangMills.Construction.RotationInvariance.RadialBumpsExistAndMollifyInC1
import YangMills.Construction.RotationInvariance.ScalarProductsOfBumpVectorsAtComplexPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane ForwardTube Filter Topology
open scoped ComplexConjugate ComplexOrder
namespace EuclideanFunctionals.GramKernelImagPosSemidef
theorem eventually_sub_timeTranslate_mem_forwardTube {w : ℂ × ℂ} (hw : w ∈ forwardTube) (r : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), w - timeTranslate (ε / r) ∈ forwardTube := by
  have hlim : Tendsto (fun ε : ℝ => ε / r) (𝓝[>] 0) (𝓝 0) := by
    have h := (continuous_id.div_const r).tendsto (0 : ℝ)
    simp only [id, zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  filter_upwards [hlim.eventually (Iio_mem_nhds hw.1), hlim.eventually (Iio_mem_nhds hw.2)]
    with ε hp hm
  have hp' : ε / r < (lightConePlus w).re := hp
  have hm' : ε / r < (lightConeMinus w).re := hm
  refine ⟨?_, ?_⟩
  · simp only [lightConePlus, timeTranslate, Prod.fst_sub, Prod.snd_sub, sub_zero] at hp' ⊢
    simp at hp' ⊢
    linarith
  · simp only [lightConeMinus, timeTranslate, Prod.fst_sub, Prod.snd_sub, sub_zero] at hm' ⊢
    simp at hm' ⊢
    linarith
theorem eventually_mem_shiftedForwardTube {n : ℕ} {z : Fin n → ℂ × ℂ} (hz : z ∈ successiveDomain n) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), z ∈ shiftedForwardTube n ε := by
  have hfirst : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ h : 0 < n, z ⟨0, h⟩ - timeTranslate (ε / 4) ∈ forwardTube := by
    by_cases h : 0 < n
    · filter_upwards [eventually_sub_timeTranslate_mem_forwardTube (hz.1 h) 4] with ε hε _
      exact hε
    · exact Eventually.of_forall fun _ h' => absurd h' h
  have hnext : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i : Fin n, ∀ h : (i : ℕ) + 1 < n,
      z ⟨(i : ℕ) + 1, h⟩ - z ⟨i, i.2⟩ - timeTranslate (ε / 2) ∈ forwardTube := by
    rw [eventually_all]
    intro i
    by_cases h : (i : ℕ) + 1 < n
    · filter_upwards [eventually_sub_timeTranslate_mem_forwardTube (hz.2 i h) 2] with ε hε _
      exact hε
    · exact Eventually.of_forall fun _ h' => absurd h' h
  filter_upwards [hfirst, hnext] with ε ha hb
  exact ⟨ha, fun i h => hb ⟨i, by omega⟩ h⟩
theorem tendsto_mollifierGramValue (hKer : PlaneKernelProps.Holds)
    (hShift : ForwardTube.GramArgsInShiftedTubes.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {ε : ℝ}
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) {ρ : ℕ+ → RealPlane → ℝ}
    (hρ : d.IsRadialMollifier ε ρ) {n n' : ℕ} (α : Fin n → realLabels)
    (α' : Fin n' → realLabels) {z : Fin n → ℂ × ℂ} {w : Fin n' → ℂ × ℂ}
    (hz : z ∈ shiftedForwardTube n ε) (hw : w ∈ shiftedForwardTube n' ε) :
    Tendsto (fun j => d.mollifierGramValue ε ρ j α α' z w) atTop
      (𝓝 (gramKernelOfPoints S z α w α')) := by
  by_cases h : 2 ≤ n + n'
  · simp only [PlaneDataWithAperture.mollifierGramValue, gramKernelOfPoints, dif_pos h]
    have hlim := (hKer m S d (n + n' - 1) (by omega)
      (fun k => gramLabelOrder α α' (Fin.cast (by omega) k))).2.2.2.2.1 ε hε.1 hε.2 ρ hρ
      {gramKernelArgs z w} isCompact_singleton
      (Set.singleton_subset_iff.2 (hShift n n' ε hε.1 hε.2 h z hz w hw))
    exact hlim.tendsto_at (Set.mem_singleton _)
  · simp only [PlaneDataWithAperture.mollifierGramValue, gramKernelOfPoints, dif_neg h]
    exact tendsto_const_nhds
theorem gramKernel_posSemidef (hMol : RadialMollifiers.ExistAndConvergeC1)
    (hKer : PlaneKernelProps.Holds) (hShift : ForwardTube.GramArgsInShiftedTubes.Holds)
    (hInner : MollifierInnerAtComplexPoints.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) :
    PositiveDefinite.KernelPosSemidefOnSet (gramKernel S) := by
  intro N t c
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a, (t a).points ∈ shiftedForwardTube (t a).length ε :=
    eventually_all.2 fun a => eventually_mem_shiftedForwardTube (t a).points_mem
  have hle : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ 1 :=
    (eventually_le_nhds (zero_lt_one' ℝ)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := eventually_mem_nhdsWithin
  obtain ⟨ε, hmem, hle1, hpos1⟩ := (hev.and (hle.and hpos)).exists
  have hε : ε ∈ Set.Ioc (0 : ℝ) 1 := ⟨hpos1, hle1⟩
  obtain ⟨ρ, hρ⟩ := (hMol m S d ε hε).1
  have hnonneg : ∀ j : ℕ+, 0 ≤ ∑ a, ∑ b, conj (c a) * c b *
      d.mollifierGramValue ε ρ j (t a).labels (t b).labels (t a).points (t b).points := by
    intro j
    have hsq : ∑ a, ∑ b, conj (c a) * c b *
        d.mollifierGramValue ε ρ j (t a).labels (t b).labels (t a).points (t b).points =
        inner ℂ (∑ a, c a • d.mollifierVector ε ρ j (t a).labels (t a).points)
          (∑ b, c b • d.mollifierVector ε ρ j (t b).labels (t b).points) := by
      rw [sum_inner]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [inner_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [inner_smul_left, inner_smul_right,
        hInner m S d ε hε ρ hρ j _ _ (t a).labels (t b).labels _ (hmem a) _ (hmem b)]
      ring
    rw [hsq, inner_self_eq_norm_sq_to_K]
    simp
  exact ge_of_tendsto' (tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ =>
    (tendsto_mollifierGramValue hKer hShift d hε hρ (t a).labels (t b).labels (hmem a) (hmem b)).const_mul _) hnonneg
theorem holds_of (hArgs : ForwardTube.GramKernelArgsFacts)
    (hShift : ForwardTube.GramArgsInShiftedTubes.Holds)
    (hKer : PlaneKernelProps.Holds) (hMol : RadialMollifiers.ExistAndConvergeC1)
    (hInner : MollifierInnerAtComplexPoints.Holds) : Holds := by
  intro m S d
  have hpsd := gramKernel_posSemidef hMol hKer hShift hInner d
  refine ⟨hpsd, fun s => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro N t c
    exact hpsd N (fun a => LabelledTuple.imagBoost s (t a)) c
  · intro p q h
    show gramKernelOfPoints S (imagBoostTuple s p.points) p.labels
      (imagBoostTuple s q.points) q.labels = _
    rw [gramKernelOfPoints, dif_pos h]
    congr 1
    funext k
    exact hArgs.2.2.2.1.2 s _ _ h _ p.points_mem _ q.points_mem k
  · intro p q hp hq
    have h : ¬ 2 ≤ p.length + q.length := by omega
    show gramKernelOfPoints S (imagBoostTuple s p.points) p.labels
      (imagBoostTuple s q.points) q.labels = 1
    rw [gramKernelOfPoints, dif_neg h, if_pos (by omega)]
  · intro p q hpq
    have h : ¬ 2 ≤ p.length + q.length := by omega
    show gramKernelOfPoints S (imagBoostTuple s p.points) p.labels
      (imagBoostTuple s q.points) q.labels = 0
    rw [gramKernelOfPoints, dif_neg h, if_neg (by omega)]
end EuclideanFunctionals.GramKernelImagPosSemidef
end YangMills.Construction
end
