# Denotational Semantics of PCF

A poor attempt at trying to write the denotational semantics of PCF. It is incomplete and mainly exists to improve my knowledge of denotational semantics and Agda.

Problems encountered:
- Mathematically, most of the functions described in denotational semantics are partial. I have not yet found a clean way of representing partial functions in Agda. Help would be very much appreciated. Partiality monad?
- I haven't put much though into defining the semantics of the fixed-point operator. It might be easier than I am imagining, but I somehow doubt that.

Ideally, I would like to use this to prove various features of the denotational semantics, such as compositionality, soundness and adequacy.
