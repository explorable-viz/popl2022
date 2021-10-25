## Cover letter

We implemented all the corrections and minor tweaks suggested by reviewers. Below we detail the few substantive changes, and also enumerate the additional minor clarifications we carried out in response to reviewers' comments.

### Substantive changes

- 2.2: introduced K to range over types of terms and types of eliminators; adjusted Fig. 4 and related exposition accordingly
- 2.2: clarify in the text that \Gamma \vdash \kappa: K is defined as the union of the typing relations for terms and eliminators (this avoids having to introduce new notation for the different typing judgements)

### Minor changes

We implemented the following changes in response to reviewer comments:

- 1.3: clarify meaning of "prefix"
- 2: slight expansion of rationale behind use of "eliminators"
- 2.2: drop phrase "partial value" and say more specifically what we mean
- 3.1: clarify that there are no complications associated with tracking dependencies on higher-order data
- 3.1: clarify what the elements in the tuples bound to the `data` field represent
- 3.1.1: remove mention of representable functors
- 3.2.2: clarify that in our implementation, the dependency functions for multiplication establish that (for non-zero n), both n * 0 and 0 * n depend only on n
- 3.4: eliminate overloaded metavariables for Galois connections and components of same
- 4.2: change yellow highlighting in Fig. 13 to (darker) blue colour, for legibility in black and white
- 4.3: state more clearly how our approach improves on differential slicing
- 4.3: change yellow highlighting in Fig. 14 to blue, to match Fig. 13

We also added the following links to supporting material:

- 1.3: add link to GitHub repository and artifact evaluation instructions
- 1.3: add link to supplementary materials (extended paper) on arXiv

### Other notes

- We elected not to distinguish the metalanguage and object language phi; to be consistent, one must also distinguish metalanguage and object language integers, which would be cumbersome.
