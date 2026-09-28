Overall outcome: COMPLETE

The exact declaration `stage3_result : Stage3S2B.MainClaim` is proved and passes the supplied entry-point checker. The proof establishes uncountability of the target class, uniform sample-free generation by the powers-of-two stream, and the feedback-resistant negative claim for every universally eventually valid fresh generator.

The negative witness uses a causal diagonal presenter whose even rounds enumerate the mandatory power-of-two core and whose odd rounds choose fresh ordinary values avoiding all prior presentations, queries, and outputs. The realized target is clean, injectively presented, complete, and belongs to the specified class. Scored outputs are confined to the core. A linear bound on the increasing target enumeration and a logarithmic bound on core prefix counts imply that the core prefix ratio tends to zero, hence the scored upper density is zero.

Material declarations used include `Stage3S2B.MainClaim`, the ordered-density definitions from `GenLimit.Core.OrderedDensity`, `Nat.nth`, `Real.log2_le_logb`, and `Real.isLittleO_logb_id_atTop`. The checked proof depends only on `propext`, `Classical.choice`, and `Quot.sound`.
