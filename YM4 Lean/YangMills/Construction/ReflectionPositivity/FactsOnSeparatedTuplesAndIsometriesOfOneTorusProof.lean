import YangMills.Construction.ReflectionPositivity.FactsOnSeparatedTuplesAndIsometriesOfOneTorus
import YangMills.Construction.ReflectionPositivity.TorusAsAMetricSpaceAndClassesOfTestFunctions
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotions
import Mathlib
set_option autoImplicit false
open scoped ENNReal Matrix
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.TorusTuples.SeparationAndSymmetry
variable {s : YangMills.Construction.Conventions.StandingParameters}
theorem dist_lt_of_torusEuclidNorm_lt {x y : s.Torus} {ε : ℝ}
    (h : YangMills.Construction.TorusMetric.torusEuclidNorm (x - y) < ε) :
    dist x y < ε := by
  obtain ⟨v₀, hv₀⟩ := TorusCutoffs.exists_proj_eq s (x - y)
  have hne : (YangMills.Construction.TorusMetric.euclidNormVec ''
      (YangMills.Construction.TorusMetric.torusProj
        (YangMills.Construction.PeriodicLattice.torusSide s.L s.m) ⁻¹' {x - y})).Nonempty :=
    ⟨_, v₀, hv₀, rfl⟩
  obtain ⟨_, ⟨v, hv, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne h
  have hv' : YangMills.Construction.TorusMetric.torusProj
      (YangMills.Construction.PeriodicLattice.torusSide s.L s.m) v = x - y := hv
  have hpos : 0 < ε := lt_of_le_of_lt (Real.sqrt_nonneg _) hlt
  rw [dist_eq_norm, pi_norm_lt_iff hpos]
  intro μ
  rw [← hv']
  refine lt_of_le_of_lt ?_ hlt
  calc ‖YangMills.Construction.TorusMetric.torusProj
        (YangMills.Construction.PeriodicLattice.torusSide s.L s.m) v μ‖ ≤ |v μ| :=
        YangMills.Construction.TorusMetric.addCircle_norm_coe_le_abs (v μ)
    _ ≤ YangMills.Construction.TorusMetric.euclidNormVec v := by
      refine Real.abs_le_sqrt ?_
      exact Finset.single_le_sum (f := fun ν => v ν ^ 2) (fun ν _ => sq_nonneg _)
        (Finset.mem_univ μ)
theorem supp_subset_tsupport (h : s.Torus → ℝ) : TorusTuples.supp (s := s) h ⊆ tsupport h := by
  intro x hx
  refine Metric.mem_closure_iff.mpr fun ε hε => ?_
  obtain ⟨y, hy, hd⟩ := (TorusTuples.mem_supp_iff h x).mp hx ε hε
  exact ⟨y, hy, dist_lt_of_torusEuclidNorm_lt hd⟩
theorem le_setDist_iff {c : ℝ≥0∞} {A B : Set s.Torus} :
    c ≤ TorusCutoffs.setDist A B ↔ ∀ a ∈ A, ∀ b ∈ B,
      c ≤ ENNReal.ofReal (YangMills.Construction.TorusMetric.torusEuclidNorm (a - b)) := by
  simp only [TorusCutoffs.setDist, YangMills.Construction.TorusMetric.setEuclidDist, le_iInf_iff]
theorem le_gap_iff {c : ℝ≥0∞} {X : TorusTuples.FnTuple s ℝ} :
    c ≤ TorusTuples.gap X ↔ ∀ l l' : Fin X.length, l ≠ l' →
      c ≤ TorusCutoffs.setDist (TorusTuples.supp (s := s) (X.get l))
        (TorusTuples.supp (s := s) (X.get l')) := by
  rw [TorusTuples.gap, Finset.le_inf_iff]
  constructor
  · intro h l l' hl
    exact h (l, l') (by simp [Finset.mem_offDiag, hl])
  · rintro h ⟨l, l'⟩ hl
    exact h l l' (Finset.mem_offDiag.mp hl).2.2
section Tuples
open YangMills.Construction.ReflectionPositivity.CutoffMirrors.TorusMetricSpace
theorem exists_pairwiseSeparated (hC : DisjointSuppSeparated (TorusTuples.unitData s))
    {X : TorusTuples.FnTuple s ℝ} (hX : TorusTuples.IsDisjointTuple X) (hlen : 1 ≤ X.length) :
    ∃ d : ℝ, 0 < d ∧
      TorusCutoffs.PairwiseSeparated (s := s)
        (fun l : Fin X.length => TorusTuples.supp (s := s) (X.get l)) d := by
  obtain ⟨d, hd, hsep⟩ := hC.1 ℝ X.length X.get hlen hX.2
  refine ⟨d, hd, fun l l' hl => ?_⟩
  refine le_setDist_iff.mpr fun a ha b hb => ?_
  have h := hsep l l' hl
  exact (le_iInf₂_iff.mp (le_iInf₂_iff.mp h a (supp_subset_tsupport _ ha))) b
    (supp_subset_tsupport _ hb)
theorem isDisjointTuple_of_pairwiseSeparated (hT : CompactMetricTorus (TorusTuples.unitData s))
    {X : TorusTuples.FnTuple s ℝ} {d : ℝ} (hd : 0 < d)
    (hL : ∀ h ∈ X, TorusTuples.IsLipschitzReal (s := s) h)
    (hp : TorusCutoffs.PairwiseSeparated (s := s)
      (fun l : Fin X.length => TorusTuples.supp (s := s) (X.get l)) d) :
    TorusTuples.IsDisjointTuple X := by
  refine ⟨fun l => hL _ (List.get_mem X l), fun l l' hl => ?_⟩
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  have h := le_setDist_iff.mp (hp l l' hl) x hx.1 x hx.2
  have h0 : YangMills.Construction.TorusMetric.torusEuclidNorm (x - x) = 0 :=
    (hT.2.1.eq_zero_iff x x).mpr rfl
  rw [h0, ENNReal.ofReal_zero] at h
  exact absurd (ENNReal.ofReal_pos.mpr hd) (not_lt.mpr h)
theorem gapPos (hC : DisjointSuppSeparated (TorusTuples.unitData s)) : GapPos s := by
  intro X hX hlen
  obtain ⟨d, hd, hp⟩ := exists_pairwiseSeparated hC hX (by omega)
  obtain ⟨l, l', hl, e⟩ := TorusTuples.exists_gap_eq hlen
  rw [e]
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hd) (hp l l' hl)
theorem disjointTuplesEqIUnion (hT : CompactMetricTorus (TorusTuples.unitData s))
    (hC : DisjointSuppSeparated (TorusTuples.unitData s)) : DisjointTuplesEqIUnion s := by
  intro n hn
  ext X
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hX, hlen⟩
    obtain ⟨d, hd, hp⟩ := exists_pairwiseSeparated hC hX (by omega)
    refine ⟨d, hd, hlen, fun h hh => ?_, hp⟩
    obtain ⟨l, rfl⟩ := List.get_of_mem hh
    exact hX.1 l
  · rintro ⟨d, hd, hlen, hL, hp⟩
    exact ⟨isDisjointTuple_of_pairwiseSeparated hT hd hL hp, hlen⟩
theorem lipTuplesSeparatedByEq (hT : CompactMetricTorus (TorusTuples.unitData s)) :
    LipTuplesSeparatedByEq s := by
  intro n _ d hd
  ext X
  constructor
  · rintro ⟨hlen, hL, hp⟩
    exact ⟨⟨isDisjointTuple_of_pairwiseSeparated hT hd hL hp, hlen⟩, le_gap_iff.mpr hp⟩
  · rintro ⟨⟨hX, hlen⟩, hsep⟩
    refine ⟨hlen, fun h hh => ?_, le_gap_iff.mp hsep⟩
    obtain ⟨l, rfl⟩ := List.get_of_mem hh
    exact hX.1 l
theorem componentsAreTestFamily (hC : DisjointSuppSeparated (TorusTuples.unitData s)) :
    ComponentsAreTestFamily s := by
  intro n hn X
  have hf := TorusTuples.isDisjointFamily_componentFamily X
  exact (hC.2 n _ hn hf.2 hf.1).1
theorem restrictionsDisjoint : RestrictionsDisjoint s := by
  rintro X Y hX ⟨J, rfl⟩
  exact (TorusTuples.isDisjointTuple_ofFn _).mpr ⟨fun _ => hX.1 _, fun _ _ hk =>
    hX.2 _ _ fun c => hk ((J.orderEmbOfFin rfl).injective c)⟩
end Tuples
theorem signedFrame_transpose (r : YangMills.Construction.PeriodicLattice.SignedFrame) :
    r.toMatrixᵀ = YangMills.Construction.PeriodicLattice.SignedFrame.toMatrix
      (r.1⁻¹, fun μ => r.2 (r.1⁻¹ μ)) := by
  ext μ ν
  simp only [Matrix.transpose_apply, YangMills.Construction.PeriodicLattice.SignedFrame.toMatrix,
    Matrix.of_apply]
  by_cases h : μ = r.1 ν
  · have h' : ν = r.1⁻¹ μ := by simp [h]
    rw [if_pos h, if_pos h', ← h']
  · have h' : ¬ ν = r.1⁻¹ μ := fun e => h (by simp [e])
    rw [if_neg h, if_neg h']
theorem mem_orthogonalGroup_of_mem_signedPermMatrices {w : Matrix (Fin 4) (Fin 4) ℝ}
    (hw : w ∈ YangMills.Construction.PeriodicLattice.signedPermMatrices) :
    w ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  obtain ⟨r, rfl⟩ := (YangMills.Construction.PeriodicLattice.mem_signedPermMatrices_iff w).mp hw
  rw [Matrix.mem_orthogonalGroup_iff', signedFrame_transpose]
  exact TorusTuples.frame_invMatrix_mul r
theorem isIntegerMatrix_of_mem_signedPermMatrices {w : Matrix (Fin 4) (Fin 4) ℝ}
    (hw : w ∈ YangMills.Construction.PeriodicLattice.signedPermMatrices) :
    YangMills.Construction.Tower.OrthogonalMotions.IsIntegerMatrix w := by
  obtain ⟨r, rfl⟩ := (YangMills.Construction.PeriodicLattice.mem_signedPermMatrices_iff w).mp hw
  intro μ ν
  by_cases h : ν = r.1 μ
  · exact ⟨r.2 μ, by simp [YangMills.Construction.PeriodicLattice.SignedFrame.toMatrix, h]⟩
  · exact ⟨0, by simp [YangMills.Construction.PeriodicLattice.SignedFrame.toMatrix, h]⟩
theorem signedMatricesAndShiftsIsometric
    (h₁ : YangMills.Construction.Tower.OrthogonalMotions.IntegerAffineDescends s.L s.m) :
    SignedMatricesAndShiftsIsometric s := by
  refine ⟨fun w hw => ?_, fun v => ?_⟩
  · obtain ⟨f, hf, hiso⟩ := h₁ w (mem_orthogonalGroup_of_mem_signedPermMatrices hw)
      (isIntegerMatrix_of_mem_signedPermMatrices hw) 0
    have e : TorusTuples.signedMatrixMap s w = f := by
      funext x
      obtain ⟨y, rfl⟩ := TorusCutoffs.exists_proj_eq s x
      rw [TorusTuples.signedMatrixMap_proj s hw]
      have := hf y
      rw [add_zero] at this
      exact this.symm
    rw [e]
    exact hiso
  · intro a b
    change YangMills.Construction.TorusMetric.torusEuclidNorm ((a + v) - (b + v)) =
      YangMills.Construction.TorusMetric.torusEuclidNorm (a - b)
    rw [add_sub_add_right_eq_sub]
theorem isometryBijectiveOrthogonal
    (hT : YangMills.Construction.ReflectionPositivity.CutoffMirrors.TorusMetricSpace.CompactMetricTorus
      (TorusTuples.unitData s))
    (h₁ : YangMills.Construction.Tower.OrthogonalMotions.TorusIsometryLifts s.L s.m) :
    IsometryBijectiveOrthogonal s := by
  intro r hr
  obtain ⟨R, hR, -, w, hw⟩ := h₁ r hr
  have hRR : R * star R = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).mp hR
  have hinj : Function.Injective r := by
    intro x y e
    have h0 : (TorusTuples.unitData s).torusDist (r x) (r y) = 0 :=
      (hT.2.1.eq_zero_iff _ _).mpr e
    have h1 : (TorusTuples.unitData s).torusDist x y = 0 := (hr x y).symm.trans h0
    exact (hT.2.1.eq_zero_iff _ _).mp h1
  have hsurj : Function.Surjective r := by
    intro x
    obtain ⟨z, rfl⟩ := TorusCutoffs.exists_proj_eq s x
    refine ⟨TorusCutoffs.proj s (star R *ᵥ (z - w)), ?_⟩
    have := hw (star R *ᵥ (z - w))
    rw [Matrix.mulVec_mulVec, hRR, Matrix.one_mulVec, sub_add_cancel] at this
    exact this
  refine ⟨Equiv.ofBijective r ⟨hinj, hsurj⟩, rfl, ?_, R, hR, w, hw⟩
  intro a b
  have h := hr ((Equiv.ofBijective r ⟨hinj, hsurj⟩).symm a)
    ((Equiv.ofBijective r ⟨hinj, hsurj⟩).symm b)
  have ea : ∀ c, r ((Equiv.ofBijective r ⟨hinj, hsurj⟩).symm c) = c :=
    fun c => (Equiv.ofBijective r ⟨hinj, hsurj⟩).apply_symm_apply c
  rw [ea, ea] at h
  exact h.symm
theorem isTorusIsometry_symm {r : s.Torus ≃ s.Torus} (hr : TorusTuples.IsTorusIsometry s r) :
    TorusTuples.IsTorusIsometry s r.symm := by
  intro a b
  have h := hr (r.symm a) (r.symm b)
  rw [r.apply_symm_apply, r.apply_symm_apply] at h
  exact h.symm
theorem uniformNorm_transport (r : s.Torus ≃ s.Torus) (h : s.Torus → ℝ) :
    YangMills.Construction.TestFunctions.uniformNorm (TorusTuples.transport r h) =
      YangMills.Construction.TestFunctions.uniformNorm h :=
  r.symm.surjective.iSup_comp fun x => ‖h x‖
theorem lipConstTorus_transport {r : s.Torus ≃ s.Torus} (hr : TorusTuples.IsTorusIsometry s r)
    (h : s.Torus → ℝ) :
    YangMills.Construction.TestFunctions.lipConstTorus
        (ℓ := YangMills.Construction.PeriodicLattice.torusSide s.L s.m) (TorusTuples.transport r h) =
      YangMills.Construction.TestFunctions.lipConstTorus
        (ℓ := YangMills.Construction.PeriodicLattice.torusSide s.L s.m) h := by
  have hd : ∀ x y : s.Torus, YangMills.Construction.TestFunctions.euclidDistTorus (r x) (r y) =
      YangMills.Construction.TestFunctions.euclidDistTorus x y := fun x y => hr x y
  unfold YangMills.Construction.TestFunctions.lipConstTorus
    YangMills.Construction.TestFunctions.bestLipschitzConstant
  congr 1
  ext C
  constructor
  · rintro ⟨h0, hc⟩
    refine ⟨h0, fun x y => ?_⟩
    have := hc (r x) (r y)
    rw [hd] at this
    simpa [TorusTuples.transport] using this
  · rintro ⟨h0, hc⟩
    refine ⟨h0, fun x y => ?_⟩
    have := hc (r.symm x) (r.symm y)
    have e := hd (r.symm x) (r.symm y)
    rw [r.apply_symm_apply, r.apply_symm_apply] at e
    rw [← e] at this
    exact this
theorem isC1_transport (hM : IsometryBijectiveOrthogonal s)
    {r : s.Torus ≃ s.Torus} (hr : TorusTuples.IsTorusIsometry s r) {h : s.Torus → ℝ}
    (hc : TorusCutoffs.IsC1 h) : TorusCutoffs.IsC1 (TorusTuples.transport r h) := by
  obtain ⟨_, _, _, R, _, w, hw⟩ := hM r.symm (isTorusIsometry_symm hr)
  rw [TorusCutoffs.isC1_iff] at hc ⊢
  have e : TorusTuples.transport r h ∘ TorusCutoffs.proj s =
      (h ∘ TorusCutoffs.proj s) ∘ fun y => R *ᵥ y + w := by
    funext y
    simp only [TorusTuples.transport, Function.comp_apply]
    rw [hw]
  rw [e]
  have hlin : ContDiff ℝ 1 fun y : Fin 4 → ℝ => R *ᵥ y :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin R)).contDiff
  exact hc.comp (hlin.add contDiff_const)
section Functions
open YangMills.Construction.ReflectionPositivity.CutoffMirrors.TorusMetricSpace
theorem isometryTransportProps (hB : IsometryActionOnFunctions (TorusTuples.unitData s))
    (hM : IsometryBijectiveOrthogonal s) : IsometryTransportProps s := by
  intro r hr h hL
  obtain ⟨-, hf, -, -⟩ := hB r.symm r.symm.bijective (isTorusIsometry_symm hr)
  obtain ⟨hsupp, -, -, hlip⟩ := hf ℝ h
  have hsup := uniformNorm_transport r h
  have hLip := lipConstTorus_transport hr h
  refine ⟨hlip hL, ?_, hsup, hLip, fun m' => ?_, isC1_transport hM hr⟩
  · rw [r.image_eq_preimage_symm]
    exact hsupp
  · change max _ _ = max _ _
    exact congrArg₂ max hsup
      (congrArg (fun t => 40 * TorusCutoffs.TorusData.sharpScale ⟨s, m'⟩ * t) hLip)
theorem setDist_image {r : s.Torus ≃ s.Torus} (hr : TorusTuples.IsTorusIsometry s r)
    (A B : Set s.Torus) :
    TorusCutoffs.setDist (r '' A) (r '' B) = TorusCutoffs.setDist A B := by
  simp only [TorusCutoffs.setDist, YangMills.Construction.TorusMetric.setEuclidDist, iInf_image]
  refine iInf_congr fun a => iInf_congr fun _ => iInf_congr fun b => iInf_congr fun _ => ?_
  exact congrArg ENNReal.ofReal (hr a b)
theorem list_get_map_cast {α β : Type*} (f : α → β) (X : List α) (l : Fin (X.map f).length) :
    (X.map f).get l = f (X.get (l.cast (List.length_map _))) := by
  simp
theorem supp_get_transportTuple (hF : IsometryTransportProps s) {r : s.Torus ≃ s.Torus}
    (hr : TorusTuples.IsTorusIsometry s r) {X : TorusTuples.FnTuple s ℝ}
    (hX : TorusTuples.IsDisjointTuple X) (l : Fin (TorusTuples.transportTuple r X).length) :
    TorusTuples.supp (s := s) ((TorusTuples.transportTuple r X).get l) =
      r '' TorusTuples.supp (s := s) (X.get (l.cast (List.length_map _))) := by
  have e : (TorusTuples.transportTuple r X).get l =
      TorusTuples.transport r (X.get (l.cast (List.length_map _))) :=
    list_get_map_cast _ X l
  rw [e]
  exact (hF r hr _ (hX.1 _)).2.1
theorem isometryTransportTupleProps (hF : IsometryTransportProps s) :
    IsometryTransportTupleProps s := by
  intro r hr X hX
  have hlen : (TorusTuples.transportTuple r X).length = X.length := List.length_map _
  refine ⟨⟨fun l => ?_, fun l l' hl => ?_⟩, ?_⟩
  · have e : (TorusTuples.transportTuple r X).get l =
        TorusTuples.transport r (X.get (l.cast (List.length_map _))) :=
      list_get_map_cast _ X l
    rw [e]
    exact (hF r hr _ (hX.1 _)).1
  · have hne : l.cast hlen ≠ l'.cast hlen := fun c => hl (Fin.cast_injective _ c)
    have h0 : TorusTuples.supp (s := s) (X.get (l.cast hlen)) ∩
        TorusTuples.supp (s := s) (X.get (l'.cast hlen)) = ∅ :=
      hX.2 _ _ hne
    change TorusTuples.supp (s := s) ((TorusTuples.transportTuple r X).get l) ∩
      TorusTuples.supp (s := s) ((TorusTuples.transportTuple r X).get l') = ∅
    rw [supp_get_transportTuple hF hr hX, supp_get_transportTuple hF hr hX,
      ← Set.image_inter r.injective]
    exact (congrArg (fun A => r '' A) h0).trans (Set.image_empty _)
  · refine eq_of_forall_le_iff fun c => ?_
    rw [le_gap_iff, le_gap_iff]
    constructor
    · intro h l l' hl
      have := h (l.cast hlen.symm) (l'.cast hlen.symm) (fun c => hl (Fin.cast_injective _ c))
      rw [supp_get_transportTuple hF hr hX, supp_get_transportTuple hF hr hX,
        setDist_image hr] at this
      exact this
    · intro h l l' hl
      rw [supp_get_transportTuple hF hr hX, supp_get_transportTuple hF hr hX, setDist_image hr]
      exact h _ _ fun c => hl (Fin.cast_injective _ c)
end Functions
theorem statement_holds (h₁ : YangMills.Construction.Tower.OrthogonalMotions.Classification)
    (h₂ : YangMills.Construction.ReflectionPositivity.CutoffMirrors.TorusMetricSpace.MetricTorusFacts) :
    Statement := by
  intro s
  obtain ⟨hT, -, hC, hB⟩ := h₂ (TorusTuples.unitData s)
  obtain ⟨-, -, hlift, hinduce⟩ := h₁.2.2.2 s.L s.m s.isAdmissible s.m.pos
  have hM := isometryBijectiveOrthogonal hT hlift
  have hF := isometryTransportProps hB hM
  exact ⟨gapPos hC, disjointTuplesEqIUnion hT hC, lipTuplesSeparatedByEq hT,
    componentsAreTestFamily hC, restrictionsDisjoint, signedMatricesAndShiftsIsometric hinduce, hM, hF,
    isometryTransportTupleProps hF⟩
end YangMills.Construction.ReflectionPositivity.TorusTuples.SeparationAndSymmetry
end
