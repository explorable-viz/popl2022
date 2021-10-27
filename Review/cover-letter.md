## Cover letter

We implemented all the corrections and minor tweaks suggested by reviewers.

In a post-response comment, Reviewer B made a good argument for retaining holes, to connect the paper to earlier work on Galois slicing. After further thought, we agree that this connection is a useful one, so instead we focused on improving the current exposition for the forward and backward analysis. We made the following specific improvements:

- clarified that the "hole-expansion" interpretation of the hole rules is shape-preserving
- explained the importance of the current dynamic function context and relationship to ambient availability
- clarified that function calls restore the dynamic context of the closure, and that is why closures capture the ambient availability

Below we enumerate the additional minor clarifications we carried out in response to reviewers' comments, and detail the one substantive change.

### Minor changes

We implemented the following changes in response to reviewer comments:

- 1.1: clarified visualisation set and input set for the Fig. 1 example
- 1.3: clarified meaning of "prefix"
- 2: slight expansion of rationale behind use of "eliminators"
- 2.2: dropped phrase "partial value" and say more specifically what we mean
- 3.1: clarified that there are no complications associated with tracking dependencies on higher-order data
- 3.1: clarified what the elements in the tuples bound to the `data` field represent
- 3.1.1: removed mention of representable functors
- 3.2.2: clarified that in our implementation, the dependency functions for multiplication establish that (for non-zero n), both n * 0 and 0 * n depend only on n
- 3.4: eliminated overloaded metavariables for Galois connections and components of same
- 4.2: changed yellow highlighting in Fig. 13 to (darker) blue colour, for legibility in black and white
- 4.3: stated more clearly how our approach improves on differential slicing
- 4.3: changed yellow highlighting in Fig. 14 to blue, to match Fig. 13

We also added the following links to supporting material:

- 1.3: link to GitHub repository and artifact evaluation instructions
- 1.3: link to supplementary materials (extended paper) on arXiv

### Substantive changes

- 2.2: introduced new arrow notation for eliminator types, to avoid confusion (esp. in Fig. 4) with arrow types of terms
- 2.2: introduced K to range over types of terms and types of eliminators; adjusted Fig. 4 and related exposition accordingly
- 2.2: clarify in the text that \Gamma \vdash \kappa: K is defined as the union of the typing relations for terms and eliminators (this avoids having to introduce new notation for the different typing judgements)

### Other notes

- We elected not to distinguish the metalanguage and object language phi; to be consistent, one must also distinguish metalanguage and object language integers, which would be cumbersome.
