We thank our three reviewers for their valuable input. We accept all their notational suggestions and do not discuss them further below.

### Reviewer A

[Fig. 1] Your understanding of the figure is exactly right, assuming you mean Fig 2, not Fig 1. We will clarify that the initial visual selection is the value of y in the record {x: "USA", y: 196.7 } passed to BarChart, and will also be specific about the visual selection induced in the LineChart. The mediating data selection consists of the orange fields highlighted in the middle of Fig 2. (Fig 1 does not involve the De Morgan dual, but shows how different visual selections induce different data selections; we will make sure this is clear.)

[L806] Indeed, the type signatures in the Galois connection for Theorem 3.8 are missing "\times \mathcal{A}" on the output (for the upper adjoint) and the input (for the lower adjoint). Theorem 3.11 (line 820) needs a similar fix.

[L1028] We will clarify that in this example the constants 2 and 3, which are omitted from the differential slice, are included by our backward analysis (because they are "needed").

### Reviewer B

[Prefixes, partial values] "Prefix" (L151) here means a partial tree, i.e. a tree from which some subtrees have been deleted. The meaning of "partial value" (L222) is actually very similar: we mean that only some initial portion (prefix) of a value is matched by an eliminator, with variables bound to the unmatched parts. We will make sure that this is as clear as possible, and avoid redundant terminology.

[Typing rule for k] Assuming you mean κ, indeed there should technically be a typing rule for κ which delegates to the judgement for e or σ as appropriate. Our overloaded typing judgement makes this hard to formulate in a non-confusing way; we will either add some clarifying text or remove the overloading so that we can add the judgement.

[Use of --> in eliminator typing judgement] We will pick a different arrow symbol for eliminator types to avoid confusion.

> line 355: please distinguish the metalanguage and object language phi.

Agreed, it is not clear here whether 𝜙(n) is intended to denote a piece of syntax or a mathematical value. A convention such as \hat{\phi} should help here.

[supporting higher-order data] There are no complications, but to support our current application we do not need to track dependencies on operations, but only "through" operations. We do expect tracking higher-order data to be important for other applications, such as extracting expression provenance; we will mention this in section 6.1.

[Figure 8 is a preorder, not a partial order] Good point! This should have been obvious from Def. 3.2. Thank you for spotting this. In fact, we feel that the presentation would actually be improved if we dropped □ (and the associated preorder). These were motivated purely by performance, but experience with our implementation has made it clear that other techniques, such as memoisation, might address this while avoiding the complexity of holes. It seems premature therefore to presuppose a hole-based approach in the paper. If our reviewers are amenable, we will simplify the presentation by dropping Fig. 8 and the various □ rules and related exposition, and use the space gained (about 3/4 of a page) to do a better job of explaining the core analysis, which as Reviewer C notes, would benefit from more clarity and some examples. (We will certainly include a note explaining how our implementation currently works, but make it clear that other choices are possible.)

[presentation of the two-point lattice] We will write the carrier as {tt, ff} and clarify the role of each.

[representable functors] Agreed, the reference could be elided with no loss of clarity.

[use \top instead of tt, L544] In fact this can only be \top, since the definition is polymorphic in A. This is a hangover from an earlier less generic formulation.

[Resugaring by Pombrio et al.] Thank you for this reference; this looks like exactly what we would like to do.

### Reviewer C

[More examples and clarity in 2.2.4+ and 3.1+] These sections are dense and would benefit from some examples. The presentational simplification we propose above (relating to □) would provide some space to do that.

[Lenses] Lenses do seem intuitively related, in that the round-tripping properties of Galois connections resemble some of the get/put laws of lenses. We are not aware of any work that establishes a formal relationship.

[Eliminators] We will make it clearer why eliminators are a good choice.

[Spacing in "e : e'" vs. "x: e".] The first operator is a cons, and the second is syntax to associate a field name with a value in a record, so the missing space is (arguably) justified here, although some prefer to write cons with no space on either side. However, it would be more consistent to write the ":" in record notation using code font, as we do with the cons.

[The paper notes that "0 * x" does not depend on "x".  Does "x * 0" depend on "x"?] "x * 0" does not depend on x either. A primitive operation such as * must provide a Galois connection for every application of * to specific arguments (section 3.2.2), and if one of the arguments is the annihilator (for operations which have one), our implementation will in that case establish a dependency only on the other argument. An (arguably) unintuitive case is that 0 * 0 must fix either one or both of the zeroes to depend on; depending on both seems inconsistent with the x * 0 case (for non-zero x), and depending on just one requires making a choice which might seem arbitrary.
