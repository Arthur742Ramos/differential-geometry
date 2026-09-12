import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Order.Real

set_option autoImplicit false

@[expose] public noncomputable section

/-!
# Maximal forward envelopes

A `ForwardPiece` is an evolution defined up to a positive finite horizon. If a
nonempty family of such pieces agrees on every common nonnegative time, this
challenge asks for one coherent envelope. Exactly one of the two constructions
is needed: a finite envelope whose endpoint is the least upper bound of all
horizons, or an immortal envelope when the horizons are unbounded.

This is the order-theoretic gluing principle used by the accompanying Ricci-flow
development. It does not itself state short-time existence, PDE regularity, or
curvature singularity results.
-/

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

end DifferentialGeometry.Palomar.MaximalForwardEnvelope

namespace DifferentialGeometry.Palomar.Submission

open MaximalForwardEnvelope

/-- Every nonempty pairwise-coherent family of positive-horizon forward pieces
has either a finite least-upper-bound envelope or an immortal envelope. -/
theorem exists_finite_or_immortal_envelope
    {A : Type*} {pieces : Set (ForwardPiece A)}
    (hne : pieces.Nonempty)
    (hagree : ∀ P ∈ pieces, ∀ Q ∈ pieces, Agrees P Q) :
    Nonempty (FiniteEnvelope pieces) ∨ Nonempty (ImmortalEnvelope pieces) := by
  sorry

end DifferentialGeometry.Palomar.Submission
