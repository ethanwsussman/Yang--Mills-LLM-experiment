import YangMills.Construction.InfiniteLattice.IsometriesAndReflectionsOfTheLatticeOfACutoff
import YangMills.Construction.InfiniteLattice.IsometriesOnPlaquetteTermsAndReflectionIdentities
import YangMills.Construction.InfiniteLattice.LatticeIsometriesAndPeriodicRealizationOnATorus
import YangMills.Construction.Lattice.ElementarySquareCorners
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MultipleReflections.SymmetriesOnFacesAndReflectionIdentities
open InfiniteLattice InfiniteLattice.LatticeSymmetry
variable {a : ℝ}
theorem actOn_actOn_of_toFun_eq {E : Type*} {r₁ r₂ r : LatticeSymmetry a}
    (h : (r₁ * r₂).toFun = r.toFun) (A : GaugeField a → E) :
    r₁.actOn (r₂.actOn A) = r.actOn A := by
  funext U
  change A (r₂.pullbackField (r₁.pullbackField U)) = A (r.pullbackField U)
  congr 1
  apply Subtype.ext
  funext b
  change U (r₁.linkMap (r₂.linkMap b)) = U (r.linkMap b)
  refine congrArg U.1 ?_
  exact InfiniteLattice.Link.ext (Subtype.ext (congrFun h _)) (Subtype.ext (congrFun h _))
theorem actOn_actOn_eq_of_toFun_eq {E : Type*} {r₁ r₂ r₃ r₄ : LatticeSymmetry a}
    (h : (r₁ * r₂).toFun = (r₃ * r₄).toFun) (A : GaugeField a → E) :
    r₁.actOn (r₂.actOn A) = r₃.actOn (r₄.actOn A) :=
  (actOn_actOn_of_toFun_eq h A).trans (actOn_actOn_of_toFun_eq rfl A).symm
theorem actOn_actOn_of_toFun_eq_id {E : Type*} {r₁ r₂ : LatticeSymmetry a}
    (h : (r₁ * r₂).toFun = id) (A : GaugeField a → E) :
    r₁.actOn (r₂.actOn A) = A := by
  funext U
  change A (r₂.pullbackField (r₁.pullbackField U)) = A U
  congr 1
  apply Subtype.ext
  funext b
  change U (r₁.linkMap (r₂.linkMap b)) = U b
  refine congrArg U.1 ?_
  exact InfiniteLattice.Link.ext (Subtype.ext (congrFun h _)) (Subtype.ext (congrFun h _))
theorem mul_toFun_apply (r₁ r₂ : LatticeSymmetry a) (x : AmbientSpace) :
    (r₁ * r₂).toFun x = r₁.toFun (r₂.toFun x) :=
  rfl
theorem timeReflect_toFun_coord (s : halfSpacingTimes a) (x : AmbientSpace) (μ : Fin 4) :
    (timeReflect s).toFun x μ =
      if μ = timeAxis then 2 * (s : ℝ) - x timeAxis else x μ := by
  rw [timeReflect_apply]
  by_cases h : μ = timeAxis
  · subst h
    simp
    ring
  · simp [h]
theorem shift_toFun_coord (v : LatticePoint a) (x : AmbientSpace) (μ : Fin 4) :
    (shift v).toFun x μ = x μ + (v : AmbientSpace) μ :=
  rfl
theorem timeAxisPoint_coord (w : spacingMultiples a) (μ : Fin 4) :
    (timeAxisPoint w : AmbientSpace) μ = if μ = timeAxis then (w : ℝ) else 0 := by
  change (Pi.single timeAxis (w : ℝ) : AmbientSpace) μ = _
  rw [Pi.single_apply]
theorem timeStep_coord (u : positiveMultiples a) (μ : Fin 4) :
    (timeStep u : AmbientSpace) μ = if μ = timeAxis then (u : ℝ) else 0 := by
  change (Pi.single timeAxis (u : ℝ) : AmbientSpace) μ = _
  rw [Pi.single_apply]
theorem timeReflect_mul_self_toFun (s : halfSpacingTimes a) :
    (timeReflect s * timeReflect s).toFun = id := by
  funext x μ
  rw [mul_toFun_apply, timeReflect_toFun_coord]
  by_cases h : μ = timeAxis
  · subst h
    simp [timeReflect_toFun_coord]
  · simp [timeReflect_toFun_coord, h]
theorem timeReflect_mul_timeReflect_toFun (s s' : halfSpacingTimes a) :
    (timeReflect s * timeReflect s').toFun =
      (shift (timeAxisPoint (doubledTimeGap s s'))).toFun := by
  funext x μ
  rw [mul_toFun_apply, shift_toFun_coord, timeAxisPoint_coord, timeReflect_toFun_coord]
  by_cases h : μ = timeAxis
  · subst h
    simp only [if_true, timeReflect_toFun_coord]
    change _ = _ + 2 * ((s : ℝ) - s')
    ring
  · simp [timeReflect_toFun_coord, h]
theorem timeReflect_mul_shift_toFun (s : halfSpacingTimes a) (w : spacingMultiples a) :
    (timeReflect s * shift (timeAxisPoint w)).toFun =
      (shift (-timeAxisPoint w) * timeReflect s).toFun := by
  funext x μ
  rw [mul_toFun_apply, mul_toFun_apply, shift_toFun_coord (-timeAxisPoint w),
    timeReflect_toFun_coord]
  have hneg : ((-timeAxisPoint w : LatticePoint a) : AmbientSpace) μ =
      -(timeAxisPoint w : AmbientSpace) μ := rfl
  rw [hneg, timeAxisPoint_coord, timeReflect_toFun_coord]
  by_cases h : μ = timeAxis
  · subst h
    simp only [if_true, shift_toFun_coord, timeAxisPoint_coord]
    ring
  · simp [shift_toFun_coord, timeAxisPoint_coord, h]
theorem timeReflect_halfTimeAdd_mul_shift_toFun (s : halfSpacingTimes a) (w : spacingMultiples a) :
    (timeReflect (halfTimeAdd s w) * shift (timeAxisPoint w)).toFun =
      (shift (timeAxisPoint w) * timeReflect s).toFun := by
  funext x μ
  rw [mul_toFun_apply, mul_toFun_apply, shift_toFun_coord (timeAxisPoint w),
    timeReflect_toFun_coord, timeAxisPoint_coord, timeReflect_toFun_coord]
  by_cases h : μ = timeAxis
  · subst h
    simp only [if_true, shift_toFun_coord, timeAxisPoint_coord]
    change 2 * ((s : ℝ) + w) - _ = _
    ring
  · simp [shift_toFun_coord, timeAxisPoint_coord, h]
theorem timeReflect_midpoint_mul_timeReflect_toFun (t : halfSpacingTimes a)
    (u : positiveMultiples a) :
    (timeReflect (midpointTime t u) * timeReflect t).toFun = (shift (timeStep u)).toFun := by
  funext x μ
  rw [mul_toFun_apply, shift_toFun_coord, timeStep_coord, timeReflect_toFun_coord]
  by_cases h : μ = timeAxis
  · subst h
    simp only [if_true, timeReflect_toFun_coord]
    change 2 * ((t : ℝ) + (u : ℝ) / 2) - _ = _
    ring
  · simp [timeReflect_toFun_coord, h]
theorem timeReflect_midpoint_mul_shift_toFun (t : halfSpacingTimes a) (u : positiveMultiples a) :
    (timeReflect (midpointTime t u) * shift (timeStep u)).toFun =
      (timeReflect t).toFun := by
  funext x μ
  rw [mul_toFun_apply, timeReflect_toFun_coord, timeReflect_toFun_coord]
  by_cases h : μ = timeAxis
  · subst h
    simp only [if_true, shift_toFun_coord, timeStep_coord]
    change 2 * ((t : ℝ) + (u : ℝ) / 2) - _ = _
    ring
  · simp [shift_toFun_coord, timeStep_coord, h]
theorem closedSquare_eq_filledSquare (p : ElementaryPlaquette a) :
    p.closedSquare = ElementarySquare.filledSquare (fun μ t => (Pi.single μ t : AmbientSpace)) a
      (p.corner : AmbientSpace) p.lowAxis p.highAxis := by
  have key : ∀ s t : ℝ, (p.corner : AmbientSpace) +
      a • (s • (Pi.single p.lowAxis 1 : AmbientSpace) + t • (Pi.single p.highAxis 1 : AmbientSpace)) =
      ElementarySquare.planePoint (fun μ t => (Pi.single μ t : AmbientSpace)) a
        (p.corner : AmbientSpace) p.lowAxis p.highAxis s t := by
    intro s t
    funext κ
    simp only [ElementarySquare.planePoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply]
    split_ifs <;> ring
  ext y
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨s, t, hs.1, hs.2, ht.1, ht.2, key s t⟩
  · rintro ⟨s, t, h0, h1, h2, h3, rfl⟩
    exact ⟨s, ⟨h0, h1⟩, t, ⟨h2, h3⟩, (key s t).symm⟩
theorem eq_of_closedSquare_eq (hC : ElementarySquare.ElementarySquareStatement)
    (D : MultipleReflections.Setup) {p q : ElementaryPlaquette D.mesh}
    (h : p.closedSquare = q.closedSquare) : p = q := by
  have hA := (hC D.L D.isAdmissible 1 0 (D.K : ℕ) le_rfl (Nat.zero_le _)).2
  have hmesh : PeriodicLattice.meshSize D.L (PeriodicLattice.levelDepth (D.K : ℕ) 0) = D.mesh := by
    simp [PeriodicLattice.levelDepth, ReflectionPositivity.AxisMirror.MirrorData.mesh]
  rw [hmesh] at hA
  obtain ⟨hb, hf, hs⟩ := (hA p.corner p.corner.2 q.corner q.corner.2 p.lowAxis p.highAxis
    q.lowAxis q.highAxis p.lowAxis_lt_highAxis q.lowAxis_lt_highAxis).2.2.2.2
    (by rw [← closedSquare_eq_filledSquare, ← closedSquare_eq_filledSquare, h])
  exact InfiniteLattice.ElementaryPlaquette.ext (Subtype.ext hb) hf hs
theorem continuous_toFun (hR : MultipleReflections.SymmetriesAndTorusPullback)
    (D : MultipleReflections.Setup) (r : D.LatticeSymmetry) : Continuous r.toFun := by
  obtain ⟨R, -, v, -, hr⟩ := ((hR D).2.1 r).1
  have : r.toFun = fun x => R x + v := funext hr
  rw [this]
  exact (R.toLinearMap.continuous_of_finiteDimensional).add continuous_const
theorem isBoundedBorelCompactlySupported_pushforwardFun
    (hR : MultipleReflections.SymmetriesAndTorusPullback) (D : MultipleReflections.Setup)
    (r : D.LatticeSymmetry)
    {E : Type} [NormedAddCommGroup E] [MeasurableSpace E] {f : AmbientSpace → E}
    (hf : IsBoundedBorelCompactlySupported f) :
    IsBoundedBorelCompactlySupported (r.pushforwardFun f) := by
  obtain ⟨s, hs₁, hs₂⟩ := (hR D).2.2.1.1 r
  have hinv : Function.invFun r.toFun = s.toFun := by
    funext y
    have h := Function.leftInverse_invFun r.toFun_injective (s.toFun y)
    rwa [hs₂ y] at h
  have hcomp : r.pushforwardFun f = f ∘ s.toFun := by
    rw [pushforwardFun, hinv]
  rw [hcomp]
  obtain ⟨hm, ⟨C, hC⟩, hc⟩ := hf
  let φ : AmbientSpace ≃ₜ AmbientSpace :=
    { toFun := s.toFun
      invFun := r.toFun
      left_inv := hs₂
      right_inv := hs₁
      continuous_toFun := continuous_toFun hR D s
      continuous_invFun := continuous_toFun hR D r }
  exact ⟨hm.comp (continuous_toFun hR D s).measurable, ⟨C, fun x => hC _⟩,
    hc.comp_homeomorph φ⟩
theorem holds (hC : ElementarySquare.ElementarySquareStatement)
    (hI : InfiniteLattice.CutoffSymmetriesAndTimeReflections)
    (hR : MultipleReflections.SymmetriesAndTorusPullback) : Statement := by
  intro D
  refine ⟨fun r => ?_, fun t u => ?_, fun s s' w => ?_⟩
  · obtain ⟨-, hplaq, hreal, hcomplex⟩ := (hI D.toStandingParameters).1 r r
    refine ⟨fun p => ?_, fun f => ?_, fun f => ?_⟩
    · obtain ⟨q₀, hq₀, hact⟩ := hplaq p
      refine ⟨⟨q₀, hq₀, fun q hq => eq_of_closedSquare_eq hC D (hq.trans hq₀.symm)⟩,
        fun q hq => ?_⟩
      rw [eq_of_closedSquare_eq hC D (hq.trans hq₀.symm)]
      exact hact
    · exact fun hf => ⟨isBoundedBorelCompactlySupported_pushforwardFun hR D r hf, hreal f hf⟩
    · exact fun hf => ⟨isBoundedBorelCompactlySupported_pushforwardFun hR D r hf, hcomplex f hf⟩
  · exact ⟨(midpointTime t u).2,
      ⟨timeReflect_midpoint_mul_timeReflect_toFun t u,
        fun A _ => actOn_actOn_of_toFun_eq (timeReflect_midpoint_mul_timeReflect_toFun t u) A⟩,
      ⟨timeReflect_midpoint_mul_shift_toFun t u,
        fun A _ => actOn_actOn_of_toFun_eq (timeReflect_midpoint_mul_shift_toFun t u) A⟩⟩
  · refine ⟨⟨timeReflect_mul_self_toFun s,
        fun A _ => actOn_actOn_of_toFun_eq_id (timeReflect_mul_self_toFun s) A⟩,
      ⟨timeReflect_mul_timeReflect_toFun s s',
        fun A _ => actOn_actOn_of_toFun_eq (timeReflect_mul_timeReflect_toFun s s') A⟩,
      ⟨timeReflect_mul_shift_toFun s w, fun A _ => ?_⟩,
      ⟨timeReflect_halfTimeAdd_mul_shift_toFun s w, fun A _ => ?_⟩⟩
    · exact actOn_actOn_eq_of_toFun_eq (timeReflect_mul_shift_toFun s w) A
    · exact actOn_actOn_eq_of_toFun_eq (timeReflect_halfTimeAdd_mul_shift_toFun s w) A
end YangMills.Construction.MultipleReflections.SymmetriesOnFacesAndReflectionIdentities
end
