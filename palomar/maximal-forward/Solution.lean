import PalomarMaximalForward.Envelope

set_option autoImplicit false

public noncomputable section

namespace DifferentialGeometry.Palomar.Submission

open MaximalForwardEnvelope

/-- Every nonempty pairwise-coherent family of positive-horizon forward pieces
has either a finite least-upper-bound envelope or an immortal envelope. -/
theorem exists_finite_or_immortal_envelope
    {A : Type*} {pieces : Set (ForwardPiece A)}
    (hne : pieces.Nonempty)
    (hagree : ∀ P ∈ pieces, ∀ Q ∈ pieces, Agrees P Q) :
    Nonempty (FiniteEnvelope pieces) ∨ Nonempty (ImmortalEnvelope pieces) :=
  MaximalForwardEnvelope.exists_finite_or_immortal_envelope hne hagree

end DifferentialGeometry.Palomar.Submission
