## Cover letter

Dear reviewers and POPL committee,

We implemented all corrections and minor tweaks suggested by reviewers, with one exception (detailed at the bottom).

In a post-response comment, Reviewer B made a good argument for retaining holes, to connect the paper to earlier work on Galois slicing. After further thought, we agree that this connection is a useful one, so we decided to retain holes, and instead focus on improving the current exposition (both for holes, and for the forward and backward analysis in general), taking an extra page to do so. We made the following specific improvements:

- 3: renamed "ambient demand [availability]" to "argument demand [availability]" to better convey its role
- 3.2: split figure for forward dependency into two for better placement of text
- 3.2.1: clarified that hole-expansion interpretation of the hole rules is shape-preserving, and gave an example
- 3.2.1: clarified why it is reasonable to think of forward-match as a function
- 3.2.2: explained importance of current dynamic function context and relationship to argument availability
- 3.2.2: explained general pattern of forward evaluation rules
- 3.2.2: clarified that function calls restore dynamic context of closure (including argument availability), and that availability of all arguments that were pattern-matched in order execute the function body are taken into account
- 3.3: split figure for backward dependency into two for better placement of text
- 3.3.2: clarify role of argument demand

Below we enumerate the additional minor clarifications carried out in response to reviewers' comments.

### Other minor changes

In addition to the various corrections, we implemented the following specific changes in response to reviewer suggestions:

- 1.1: clarified visualisation set and input set for the Fig. 1 example
- 1.1: clarified that Fig. 1 shows how different visual selections induce different data selections
- 1.1: clarified second visualisation set for Fig. 2 example
- 1.3: clarified meaning of "prefix"
- 2: clarified rationale behind use of eliminators
- 2.2: dropped phrase "partial value" and said more specifically what we mean
- 2.2: introduced new arrow notation for eliminator types, to avoid confusion (esp. in Fig. 4) with arrow types of terms
- 2.2: introduced K to range over types of terms and types of eliminators; adjusted Fig. 4 and related exposition accordingly
- 2.2: clarified in the text that \Gamma \vdash \kappa: K is defined as the union of the typing relations for terms and eliminators (this avoids having to introduce new notation for the different typing judgements)
- 2.2.4: gave an example of pattern-matching using eliminators
- 3.1: clarified that there are no complications associated with tracking dependencies on higher-order data
- 3.1: clarified what the elements in the tuples bound to the `data` field represent
- 3.1.1: removed mention of representable functors
- 3.2.2: clarified that in our implementation, the dependency functions for multiplication establish that (for non-zero n), both n * 0 and 0 * n depend only on n
- 3.4: eliminated overloaded metavariables for Galois connections and components of same
- 4.2: changed yellow highlighting in Fig. 13 to (darker) blue colour, for legibility in black and white
- 4.3: stated more clearly how our approach improves on differential slicing
- 4.3: changed yellow highlighting in Fig. 14 to blue, to match Fig. 13
- 6.1: mentioned tracking dependencies on higher-order data in relation to expression provenance

We also added the following links to supporting material:

- 1.3: link to GitHub repository and artifact evaluation instructions
- 1.3: link to supplementary materials (extended paper) on arXiv

### Other notes

We elected not to distinguish metalanguage and object language phi. Although we are sympathetic to the suggestion, to be consistent one should also distinguish metalanguage and object language integers. We felt this would be cumbersome, so we elected to retain the existing implicit coercion between metalanguage and object language for primitive constants (nullary or otherwise).
