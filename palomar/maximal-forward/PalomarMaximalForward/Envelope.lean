import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Order.Real

set_option autoImplicit false

public noncomputable section

namespace DifferentialGeometry.Palomar.MaximalForwardEnvelope

open Set

/-- A partial forward evolution with a positive finite time horizon. -/
structure ForwardPiece (A : Type*) where
  horizon : Real
  horizon_pos : 0 < horizon
  value : Real → A

/-- Two forward pieces agree wherever both are defined at nonnegative time. -/
def Agrees {A : Type*} (P Q : ForwardPiece A) : Prop :=
  ∀ t, 0 ≤ t → t < P.horizon → t < Q.horizon → P.value t = Q.value t

/-- The set of time horizons represented by a family of forward pieces. -/
def Horizons {A : Type*} (pieces : Set (ForwardPiece A)) : Set Real :=
  ForwardPiece.horizon '' pieces

/-- A coherent envelope on a positive finite maximal interval. -/
structure FiniteEnvelope {A : Type*} (pieces : Set (ForwardPiece A)) where
  endpoint : Real
  endpoint_pos : 0 < endpoint
  value : Real → A
  endpoint_isLUB : IsLUB (Horizons pieces) endpoint
  covers : ∀ t, 0 ≤ t → t < endpoint →
    ∃ P ∈ pieces, t < P.horizon
  restricts : ∀ P ∈ pieces, ∀ t, 0 ≤ t → t < P.horizon →
    value t = P.value t

/-- A coherent envelope defined for every nonnegative time. -/
structure ImmortalEnvelope {A : Type*} (pieces : Set (ForwardPiece A)) where
  value : Real → A
  horizons_unbounded : ¬ BddAbove (Horizons pieces)
  covers : ∀ t, 0 ≤ t → ∃ P ∈ pieces, t < P.horizon
  restricts : ∀ P ∈ pieces, ∀ t, 0 ≤ t → t < P.horizon →
    value t = P.value t

private structure CoverAt {A : Type*}
    (pieces : Set (ForwardPiece A)) (t : Real) where
  piece : ForwardPiece A
  mem : piece ∈ pieces
  before : t < piece.horizon

/-- A nonempty pairwise-coherent family of positive-horizon forward pieces has
either a finite envelope at the least upper bound of its horizons or an
immortal envelope covering every nonnegative time. -/
theorem exists_finite_or_immortal_envelope
    {A : Type*} {pieces : Set (ForwardPiece A)}
    (hne : pieces.Nonempty)
    (hagree : ∀ P ∈ pieces, ∀ Q ∈ pieces, Agrees P Q) :
    Nonempty (FiniteEnvelope pieces) ∨ Nonempty (ImmortalEnvelope pieces) := by
  classical
  by_cases hbdd : BddAbove (Horizons pieces)
  · left
    let omega := sSup (Horizons pieces)
    have hhorizons_nonempty : (Horizons pieces).Nonempty := by
      rcases hne with ⟨P, hP⟩
      exact ⟨P.horizon, ⟨P, hP, rfl⟩⟩
    have hlub : IsLUB (Horizons pieces) omega :=
      isLUB_csSup hhorizons_nonempty hbdd
    have homega_pos : 0 < omega := by
      rcases hne with ⟨P, hP⟩
      exact P.horizon_pos.trans_le (hlub.1 ⟨P, hP, rfl⟩)
    have hcover : ∀ t, 0 ≤ t → t < omega → Nonempty (CoverAt pieces t) := by
      intro t _ht0 ht
      rcases exists_lt_of_lt_csSup hhorizons_nonempty ht with ⟨T, hT, htT⟩
      rcases hT with ⟨P, hP, rfl⟩
      exact ⟨⟨P, hP, htT⟩⟩
    let cover (t : Real) (ht0 : 0 ≤ t) (ht : t < omega) : CoverAt pieces t :=
      Classical.choice (hcover t ht0 ht)
    let seed : ForwardPiece A := Classical.choose hne
    let g : Real → A := fun t =>
      if ht : 0 ≤ t ∧ t < omega then (cover t ht.1 ht.2).piece.value t
      else seed.value t
    refine ⟨⟨omega, homega_pos, g, hlub, ?_, ?_⟩⟩
    · intro t ht0 ht
      exact ⟨(cover t ht0 ht).piece, (cover t ht0 ht).mem, (cover t ht0 ht).before⟩
    · intro P hP t ht0 htP
      have hPomega : P.horizon ≤ omega := hlub.1 ⟨P, hP, rfl⟩
      have htomega : t < omega := htP.trans_le hPomega
      have hdom : 0 ≤ t ∧ t < omega := ⟨ht0, htomega⟩
      simpa only [g, dif_pos hdom] using
        (hagree (cover t ht0 htomega).piece (cover t ht0 htomega).mem P hP
          t ht0 (cover t ht0 htomega).before htP)
  · right
    have hcover : ∀ t, 0 ≤ t → Nonempty (CoverAt pieces t) := by
      intro t _ht0
      have hexists : ∃ T ∈ Horizons pieces, t < T := by
        by_contra hnot
        apply hbdd
        refine ⟨t, ?_⟩
        intro T hT
        by_contra hnle
        exact hnot ⟨T, hT, lt_of_not_ge hnle⟩
      rcases hexists with ⟨T, ⟨P, hP, rfl⟩, htT⟩
      exact ⟨⟨P, hP, htT⟩⟩
    let cover (t : Real) (ht0 : 0 ≤ t) : CoverAt pieces t :=
      Classical.choice (hcover t ht0)
    let seed : ForwardPiece A := Classical.choose hne
    let g : Real → A := fun t =>
      if ht : 0 ≤ t then (cover t ht).piece.value t else seed.value t
    refine ⟨⟨g, hbdd, ?_, ?_⟩⟩
    · intro t ht0
      exact ⟨(cover t ht0).piece, (cover t ht0).mem, (cover t ht0).before⟩
    · intro P hP t ht0 htP
      simpa only [g, dif_pos ht0] using
        (hagree (cover t ht0).piece (cover t ht0).mem P hP
          t ht0 (cover t ht0).before htP)

end DifferentialGeometry.Palomar.MaximalForwardEnvelope
