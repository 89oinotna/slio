This package contains a simple implementation for
SLIO; an extension to LIO for enforcing dynamic
policies.

In this package you find:
- SimpleStLIO  -- The simple implementation of SLIO
  (limited IO functionality).
- DCLabels, DLM, Flowlocks, NonDisclosurePol and
  TwoPoint  -- Encodings of various policy
  specification frameworks in SLIO. The DCLabels
  encoding uses code from the original LIO, located
  in the folder DCLabels/
- explore/  -- A folder containing code samples used
  in the paper "Dynamic Enforcement of Dynamic
  Policies".
  
### SLIO
- Parametrized on label format and policy state.
- Labels dont have to form a lattice
  - (reflexive and transitive) ⊑ :: S -> l1:L -> l2:L -> Bool which checks if the flow from l1 to l2 is allowed in the state
- lset (lcurr) is the set of labels  present in the computation
  - reading: when an information becomes accessible then lset is extended with the information label as set union
  - writing: when writing it checks that ∀l ∈ lset ⇒ l ⊑s lr so that if all the labels in the computation are allowed to flow to the label we are writing
- policy changes: checks if the new state does not allow flows from labels in lset that were previously disallowed (to prevent conditionally allowing flows) by checking if ∀l ∈ lset ⇒ ¬(incUpperSet s1 s2 l)
