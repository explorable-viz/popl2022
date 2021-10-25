## Cover letter

### Substantive changes

- Introduced K to range over types of terms and types of eliminators; adjusted Fig. 4 and related exposition accordingly
- Clarify in the text that \Gamma \vdash \kappa: K is defined as the union of the typing relations for terms and eliminators. (Providing a separate judgement would mean avoiding overloading the typing judgement symbol.)

### Minor changes

- add link to GitHub repository and artifact evaluation instructions
- add link to supplementary materials (extended paper) on arXiv
- 3.1 clarify what the elements in the tuples bound to the `data` field represent
- 3.3.1 remove mention of representable functors
- eliminate overloaded metavariables for Galois connections and components of same
- clarify that there are no complications associated with tracking dependencies on higher-order data
- state more clearly in section 4.3 how our approach improves on differential slicing
- clarify that the approach supports an analysis for primitive operations where (for non-zero n), both n * 0 and 0 * n only depend on n
- clarify meaning of "prefix" in section 1.3
- drop the phrase "partial value" from the intro to 2.2 and say more specifically what we mean
- change yellow highlighting in Figs. 13 and 14 to (darker) blue colour, for legibility in black and white

### Other notes

- We elected not to distinguish the metalanguage and object language phi; to be consistent, one must also distinguish metalanguage and object language integers, which would be cumbersome.
